open Jasmin
open Cmdliner
open CommonCLI
open Utils

let get_outfile_name outfile =
  match outfile with
  | None -> ""
  | Some f -> 
        let basename = Filename.basename f in
        let basename' =
          try Filename.chop_extension basename with Invalid_argument _ -> basename in
        String.capitalize_ascii basename'

let format_to_file outfile action =
  let fmt, close =
    match outfile with
    | None ->
        Format.std_formatter, (fun () -> ())
    | Some f ->
        let out = open_out f in
        let fmt = Format.formatter_of_out_channel out in
        fmt, (fun () -> close_out out)
  in
  try
    BatPervasives.finally
      (fun () -> close ())
      (fun () -> action fmt)
      ()
  with e ->
    BatPervasives.ignore_exceptions
      (fun () -> Option.map Unix.unlink outfile)
      ();
    raise e

let extract_to_file prog arch pd msfsz asmOp model amodel fnames array_dir outfile prooffile =
  let array_dir =
    if array_dir = None then Option.map Filename.dirname outfile else array_dir
  in
  let extract () =
    format_to_file outfile (fun fmt ->
      ToEC.extract prog arch pd msfsz asmOp model amodel fnames array_dir fmt) in
  let extract_proof () =
    format_to_file prooffile (fun fmt ->
      ToEC.generate_safety_lemmas (get_outfile_name outfile) prog arch pd msfsz asmOp model amodel fnames array_dir fmt) in
  match model, outfile, prooffile with
  | SafetyAnnotations, None, Some _ -> extract_proof ()
  | SafetyAnnotations, Some _, None -> extract ()
  | SafetyAnnotations, _, _         -> extract (); extract_proof ()
  | _ -> extract ()

(* [defined_under idirs idents f]: is the function [f] defined in a file
   located under the directory bound to one of [idents] by [-I IDENT=path]? *)
let defined_under idirs idents =
  let realpath p = try Unix.realpath p with Unix.Unix_error _ -> p in
  let dir ident =
    match List.assoc_opt ident idirs with
    | Some d ->
        let d = realpath d in
        if Stdlib.String.ends_with ~suffix:Filename.dir_sep d then d
        else d ^ Filename.dir_sep
    | None ->
        hierror ~loc:Lnone ~kind:"command-line error"
          "--safety-simplify-from=%s: %s is not bound by -I %s=PATH" ident ident ident
  in
  let dirs = List.map dir idents in
  let memo = Hashtbl.create 17 in
  fun (f : (_, _) Prog.func) ->
    let file = f.Prog.f_loc.Location.loc_fname in
    let file =
      match Hashtbl.find_opt memo file with
      | Some r -> r
      | None -> let r = realpath file in Hashtbl.add memo file r; r
    in
    List.exists (fun prefix -> Stdlib.String.starts_with ~prefix file) dirs

let parse_and_extract arch call_conv idirs =
  let module A = (val CoreArchFactory.get_arch_module arch call_conv) in
  let extract model amodel no_simplify simplify_from functions array_dir output output_proof pass file =
    let safety =
      match model with
       | SafetyAnnotations -> true
       | _ -> false
    in
    (* with --no-safety-simplify, only the functions defined under the
       includes of --safety-simplify-from are simplified *)
    let safety_simplify =
      if safety && no_simplify then Some (defined_under idirs simplify_from)
      else None
    in
    let prog =
      parse_and_compile (module A) ~wi2i:true ~safety
        ?safety_simplify pass file idirs in
    (* the unsimplified functions never share their auxiliary variables *)
    ToEC.fresh_aux_for :=
      (match safety_simplify with
       | None -> fun _ -> false
       | Some simplify_f ->
           let fresh =
             List.fold_left
               (fun s f -> if simplify_f f then s else Prog.Sf.add f.Prog.f_name s)
               Prog.Sf.empty (snd prog)
           in
           fun fn -> Prog.Sf.mem fn fresh);
    extract_to_file prog arch A.reg_size  A.msf_size A.asmOp model amodel functions
      array_dir output output_proof
  in
  fun model amodel no_simplify simplify_from functions array_dir output output_proof pass file warn ->
    if not warn then nowarning ();
    match extract model amodel no_simplify simplify_from functions array_dir output output_proof pass file with
    | () -> ()
    | exception HiError e ->
        Format.eprintf "%a@." pp_hierror e;
        exit 1

let model =
  let alts =
    [ ("normal", Normal); ("CT", ConstantTime); ("CTG", ConstantTimeGlobal); ("safety", SafetyAnnotations)]
  in
  (* TODO : fix the documentation *)
  let doc =
    "Extraction model.
    $(b,normal): plain extraction.
    $(b,CT): Functions additionally return timing-observable leakage for
    'cryptographic constant time' (if/while conditions, memory access
    addresses, array indices, for loop bounds).
    $(b,safety): extract for safety verification.
    (Deprecated) $(b,CTG): Cryptographic constant time leakage is added to a
    global variable."
  in
  Arg.(value & opt (Arg.enum alts) Normal & info [ "m"; "model" ] ~doc)

let array_model =
  let alts =
    [ ("old", ToEC.ArrayOld); ("warray", ToEC.WArray); ("barray", ToEC.BArray) ]
  in

  let doc =
    "Array model.
     $(b,warray): use polymorphic arrays and warrays (functions predefined in eclib).
     $(b,barray): use byte arrays (functions predefined in eclib).
     (Deprecated) $(b,old): old representation for array operations (anonymous functions instead of eclib functions)."
  in
  Arg.(value & opt (Arg.enum alts) ToEC.BArray & info [ "array-model" ] ~doc)

let no_safety_simplify =
  let doc =
    "Safety model only: do not simplify the instrumented program (no final \
     constant propagation nor dead-code elimination). Every safety assertion is \
     kept, including the statically true ones, and expressions and branches that \
     only depend on compile-time values (e.g. $(i,param) declarations) are left \
     unevaluated; the initialisations of the init-tracking variables, the \
     numbering of variables and the auxiliary variables of the extraction do \
     not depend on array sizes. The shape of the extracted \
     program then does not depend on the values of the parameters, which is what \
     parametric safety proofs need."
  in
  Arg.(value & flag & info [ "no-safety-simplify" ] ~doc)

let safety_simplify_from =
  let doc =
    "With $(b,--no-safety-simplify): functions defined in files reached \
     through the include $(docv) (of $(b,-I) $(docv)=path) are nevertheless \
     simplified in the standard way, so that their extraction matches the one \
     of a library extracted without $(b,--no-safety-simplify) (e.g. the \
     formosa-keccak safety models). This option may be repeated."
  in
  Arg.(value & opt_all string [] & info [ "safety-simplify-from" ] ~docv:"IDENT" ~doc)

let functions =
  let doc =
    "Only extract the given function (and its dependencies). This argument may \
     be extract to check many functions. If not given, all functions will be \
     extracted."
  in
  Arg.(value & opt_all string [] & info [ "f"; "function" ] ~doc)

let output =
  let doc = "Output file. If not given, output will be printed on stdout." in
  Arg.(
    value
    & opt (some string) None
    & info [ "o"; "output" ] ~docv:"OUTPUT FILE" ~doc)

let output_proof =
 let doc = "Output proof file. If not given, output will be printed on stdout." in
  Arg.(
    value
    & opt (some string) None
    & info [ "output-proof" ] ~docv:"OUTPUT PROOF FILE" ~doc)

let array_dir =
  let doc =
    "Directory for generation of easycrypt array theories. \
     If not given, the theories be in the same directory as the output \
     (they will not be generated if the output is stdout)."
  in
  Arg.(
    value
    & opt (some dir) None
    & info [ "oa"; "output-array" ] ~docv:"OUTPUT DIR" ~doc)

let file =
  let doc = "The Jasmin source file to extract" in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"JAZZ" ~doc)

let () =
  let doc = "Extract Jasmin program to easycrypt" in
  let man =
    [
      `S Manpage.s_environment;
      Manpage.s_environment_intro;
      `I ("OCAMLRUNPARAM", "This is an OCaml program");
      `I ("JASMINPATH", "To resolve $(i,require) directives");
    ]
  in
  let info =
    Cmd.info "jasmin2ec" ~version:Glob_options.version_string ~doc ~man
  in
  Cmd.v info
    Term.(
      const parse_and_extract $ arch $ call_conv $ idirs $ model $ array_model
      $ no_safety_simplify $ safety_simplify_from $ functions $ array_dir
      $ output $ output_proof
      $ after_pass $ file $ warn)
  |> Cmd.eval |> exit
