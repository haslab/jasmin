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

(* [defined_under idirs idents fname]: is the file [fname] located under the
   directory bound to one of [idents] by [-I IDENT=path]? *)
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
  fun file ->
    let file =
      match Hashtbl.find_opt memo file with
      | Some r -> r
      | None -> let r = realpath file in Hashtbl.add memo file r; r
    in
    List.exists (fun prefix -> Stdlib.String.starts_with ~prefix file) dirs

let parse_and_extract arch call_conv idirs =
  let module A = (val CoreArchFactory.get_arch_module arch call_conv) in
  let extract model amodel no_simplify symbolic simplify_from functions array_dir output output_proof pass file =
    let safety =
      match model with
       | SafetyAnnotations -> true
       | _ -> false
    in
    if safety && no_simplify && symbolic then
      hierror ~loc:Lnone ~kind:"command-line error"
        "--no-safety-simplify and --safety-symbolic-params are exclusive";
    (* with --no-safety-simplify or --safety-symbolic-params, the functions
       defined under the includes of --safety-simplify-from keep the standard
       treatment *)
    let in_libs =
      if safety && (no_simplify || symbolic) then defined_under idirs simplify_from
      else fun _ -> false
    in
    let in_lib f = in_libs f.Prog.f_loc.Location.loc_fname in
    let safety_simplify = if safety && no_simplify then Some in_lib else None in
    let safety_symbolic =
      if safety && symbolic then Some (fun f -> not (in_lib f)) else None in
    let prog =
      parse_and_compile (module A) ~wi2i:true ~safety
        ?safety_simplify ?safety_symbolic pass file idirs in
    (* the other functions never share their auxiliary variables *)
    ToEC.fresh_aux_for :=
      (if safety && (no_simplify || symbolic) then
         let fresh =
           List.fold_left
             (fun s f -> if in_lib f then s else Prog.Sf.add f.Prog.f_name s)
             Prog.Sf.empty (snd prog)
         in
         fun fn -> Prog.Sf.mem fn fresh
       else fun _ -> false);
    extract_to_file prog arch A.reg_size  A.msf_size A.asmOp model amodel functions
      array_dir output output_proof
  in
  fun model amodel no_simplify symbolic simplify_from functions array_dir output output_proof pass file warn ->
    if not warn then nowarning ();
    match extract model amodel no_simplify symbolic simplify_from functions array_dir output output_proof pass file with
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

let safety_symbolic_params =
  let doc =
    "Safety model only: keep the parameters symbolic through the safety \
     instrumentation and its simplification (constant propagation and \
     dead-code elimination), and substitute their values afterwards (integer \
     parameters as numerals). Outside of the size positions (types and the \
     arguments of $(i,is_arr_init)), every occurrence of a $(i,param) stands \
     for a value that the simplification cannot evaluate, and so does, in the \
     branches of a conditional that depends on parameters, the literal offset \
     of an access to a parameter-sized array: the simplified program has the \
     same shape at every value of the parameters, while everything that does \
     not depend on them is simplified as usual. The initialisations of the \
     init-tracking variables, the numbering of variables and the auxiliary \
     variables are made independent of array sizes as with \
     $(b,--no-safety-simplify), which this option excludes."
  in
  Arg.(value & flag & info [ "safety-symbolic-params" ] ~doc)

let safety_simplify_from =
  let doc =
    "With $(b,--no-safety-simplify) or $(b,--safety-symbolic-params): \
     functions defined in files reached through the include $(docv) (of \
     $(b,-I) $(docv)=path) nevertheless get the standard treatment, so that \
     their extraction matches the one of a library extracted without these \
     options (e.g. the formosa-keccak safety models). This option may be \
     repeated."
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
      $ no_safety_simplify $ safety_symbolic_params $ safety_simplify_from
      $ functions $ array_dir
      $ output $ output_proof
      $ after_pass $ file $ warn)
  |> Cmd.eval |> exit
