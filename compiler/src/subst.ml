open Utils
open Prog
open Operators
module L = Location

(* When there is no location, we report an internal error. *)
let hierror ?loc fmt =
  let h = hierror ~kind:"compilation error" ~sub_kind:"param expansion" in
  match loc with
  | None -> h ~loc:Lnone ~internal:true fmt
  | Some loc -> h ~loc:(Lone loc) fmt

let gsubst_ty (flen: 'len1 -> 'len2) ty =
  match ty with
  | Bty ty -> Bty ty
  | Arr(ty, e) -> Arr(ty, flen e)

let rec gsubst_e (flen: ?loc:L.t -> 'len1 -> 'len2) (f: 'len1 ggvar -> 'len2 gexpr) (e: 'len1 gexpr) : 'len2 gexpr =
  match e with
  | Pconst c -> Pconst c
  | Pbool b  -> Pbool b
  | Parr_init (ws, n) -> Parr_init (ws, flen n)
  | Pvar v -> f v
  | Pget (al, aa, ws, v, e) -> Pget(al, aa, ws, gsubst_gvar f v, gsubst_e flen f e)
  | Psub (aa, ws, len, v, e) -> Psub(aa,ws,flen ~loc:(L.loc v.gv) len, gsubst_gvar f v, gsubst_e flen f e)
  | Pload (al, ws, e) -> Pload (al, ws, gsubst_e flen f e)
  | Papp1 (o, e)     -> Papp1 (o, gsubst_e flen f e)
  | Papp2 (o, e1, e2)-> Papp2 (o, gsubst_e flen f e1, gsubst_e flen f e2)
  | PappN (o, es) -> PappN (o, List.map (gsubst_e flen f) es)
  | Pif   (ty, e, e1, e2)-> Pif(gsubst_ty (flen ?loc:None) ty, gsubst_e flen f e, gsubst_e flen f e1, gsubst_e flen f e2)
  | Pbig (e, o, x, e1, e2, e0) ->
    Pbig(gsubst_e flen f e,
         o,
         gsubst_vdest f x,
         gsubst_e flen f e1,
         gsubst_e flen f e2,
         gsubst_e flen f e0)
  | Pis_var_init v -> Pis_var_init (gsubst_vdest f v)
  | Pis_mem_init (e1,e2) -> Pis_mem_init (gsubst_e flen f e1,gsubst_e flen f e2)

and gsubst_gvar f v =
  match f v with
  | Pvar v -> v
  | _      -> assert false

and gsubst_vdest f v =
  let v = gsubst_gvar f (gkvar v) in
  assert (is_gkvar v);
  v.gv

let gsubst_lval (flen: ?loc:L.t -> 'len1 -> 'len2) f lv =
  match lv with
  | Lnone(i,ty)  -> Lnone(i, gsubst_ty (flen ~loc:i) ty)
  | Lvar v       -> Lvar (gsubst_vdest f v)
  | Lmem (al, w,vi,e) -> Lmem(al, w, vi, gsubst_e flen f e)
  | Laset(al, aa,w,v,e) -> Laset(al, aa, w, gsubst_vdest f v, gsubst_e flen f e)
  | Lasub(aa,w,len,v,e) -> Lasub(aa, w, flen ~loc:(L.loc v) len, gsubst_vdest f v, gsubst_e flen f e)

let gsubst_lvals flen f  = List.map (gsubst_lval flen f)
let gsubst_es flen f = List.map (gsubst_e flen f)

let rec gsubst_i (flen: ?loc:L.t -> 'len1 -> 'len2) f i =
  let i_desc =
    match i.i_desc with
    | Cassgn(x, tg, ty, e) ->
      let e = gsubst_e flen f e in
      let x = gsubst_lval flen f x in
      let ty = gsubst_ty (flen ?loc:None) ty in
      Cassgn(x, tg, ty, e)
    | Copn(x,t,o,e)   -> Copn(gsubst_lvals flen f x, t, o, gsubst_es flen f e)
    | Csyscall(x,o,e)   -> Csyscall(gsubst_lvals flen f x, o, gsubst_es flen f e)
    | Cassert (msg, e)  -> Cassert (msg, gsubst_e flen f e)
    | Cif(e,c1,c2)  -> Cif(gsubst_e flen f e, gsubst_c flen f c1, gsubst_c flen f c2)
    | Cfor(x,(d,e1,e2),c) ->
        Cfor(gsubst_vdest f x, (d, gsubst_e flen f e1, gsubst_e flen f e2), gsubst_c flen f c)
    | Cwhile(a, c, e, loc, c') ->
      Cwhile(a, gsubst_c flen f c, gsubst_e flen f e, loc, gsubst_c flen f c')
    | Ccall(x,fn,e) -> Ccall(gsubst_lvals flen f x, fn, gsubst_es flen f e) in
  { i with i_desc }

and gsubst_c flen f c = List.map (gsubst_i flen f) c

let gsubst_cf_cond flen f =
  List.map (fun (prover,clause) -> prover, gsubst_e flen f clause)

let gsubst_cf_contra flen f c =
  Some
  {
    f_iparams = List.map (gsubst_vdest f) c.f_iparams;
    f_ires = List.map (gsubst_vdest f) c.f_ires;
    f_pre = gsubst_cf_cond flen f c.f_pre;
    f_post = gsubst_cf_cond flen f c.f_post;
  }

let gsubst_func (flen: ?loc:L.t -> 'len1 -> 'len2) f fc =
  let dov v = L.unloc (gsubst_vdest f (L.mk_loc L._dummy v)) in
  { fc with
    f_tyin = List.map (gsubst_ty (flen ?loc:None)) fc.f_tyin;
    f_contra = Option.bind fc.f_contra (gsubst_cf_contra flen f);
    f_args = List.map dov fc.f_args;
    f_body = gsubst_c flen f fc.f_body;
    f_tyout = List.map (gsubst_ty (flen ?loc:None)) fc.f_tyout;
    f_ret  = List.map (gsubst_vdest f) fc.f_ret
  }

let subst_func f fc =
  gsubst_func (fun ?loc:_ ty -> ty)
     (fun v -> if is_gkvar v then f v.gv else Pvar v) fc

(* ---------------------------------------------------------------- *)

type psubst = pexpr_ ggvar -> pexpr

let rec psubst_e (f: psubst) (e: pexpr) : pexpr =
  gsubst_e (psubst_e_ f) f e
and psubst_e_ f ?loc:_ (PE e) = PE (psubst_e f e)

let psubst_ty f (ty: pty) : pty =
  match ty with
  | Bty ty -> Bty ty
  | Arr(ty, e) -> Arr(ty, psubst_e_ f e)

let psubst_v subst =
  let subst = ref subst in
  let rec aux v : pexpr =
    let k = v.gs in
    let v = v.gv in
    let v_ = v.L.pl_desc in
    let e =
      try Mpv.find v_ !subst
      with Not_found ->
        assert (not (PV.is_glob v_));
        let ty = psubst_ty aux v_.v_ty in
        let v' = PV.mk v_.v_name v_.v_kind ty v_.v_dloc v_.v_annot in
        let v = {v with L.pl_desc = v'} in
        let v = { gv = v; gs = k } in
        let e = Pvar v in
        subst := Mpv.add v_ e !subst;
        e in
    match e with
    | Pvar x ->
      let k = x.gs in
      let x = {x.gv with L.pl_loc = L.loc v} in
      let x = {gv = x; gs = k} in
      Pvar x
    | _      -> e in
  aux

let psubst_ge f = function
  | GEword e -> GEword (psubst_e f e)
  | GEarray es -> GEarray (List.map (psubst_e f) es)

(* ---------------------------------------------------------------- *)
(* Simplify type                                                    *)
let int_of_op1 ?loc =
  function
  | Oneg Op_int -> Z.neg
  | o -> hierror ?loc "unary operator %s not supported in array sizes" (PrintCommon.string_of_op1 ~debug:false o)

let shift_left ?loc (x: Z.t) (y: Z.t) : Z.t =
  match Z.to_int y with
  | exception Z.Overflow -> hierror ?loc "overflow in left shift by %s" (Z.to_string y)
  | y -> if y < 0 then Z.shift_right x (-y) else Z.shift_left x y

let shift_right ?loc (x: Z.t) (y: Z.t) : Z.t =
  match Z.to_int y with
  | exception Z.Overflow -> hierror ?loc "overflow in right shift by %s" (Z.to_string y)
  | y -> if y < 0 then Z.shift_left x (-y) else Z.shift_right x y

let zremu (x : Z.t) (y : Z.t) = Z.(of_int (sign y) * erem (of_int (sign y) * x) y)

let int_of_op2 ?loc o =
  match o with
  | Oadd Op_int -> Z.add
  | Omul Op_int -> Z.mul
  | Osub Op_int -> Z.sub
  | Odiv(sg, Op_int) -> if sg = Unsigned then Z.fdiv else Z.div
  | Omod(sg, Op_int) -> if sg = Unsigned then zremu else Z.rem
  | Olsl Op_int -> shift_left ?loc
  | Oasr Op_int -> shift_right ?loc
  | _     -> hierror ?loc "operator %s not allowed in array size (only standard arithmetic operators and modulo are allowed)" (PrintCommon.string_of_op2 o)

let rec int_of_expr ?loc e =
  match e with
  | Pconst i -> i
  | Papp1 (o, e1) ->
     int_of_op1 ?loc o @@ int_of_expr ?loc e1
  | Papp2 (o, e1, e2) ->
      let op = int_of_op2 ?loc o in
      op (int_of_expr ?loc e1) (int_of_expr ?loc e2)
  | Pbool _ | Parr_init _ | Pvar _ | Pis_var_init _ | Pis_mem_init _
  | Pget _ | Psub _ | Pload _ | PappN _ | Pif _ | Pbig _ ->
      hierror ?loc "expression %a not allowed in array size (only constant arithmetic expressions are allowed)" (Printer.pp_pexpr ~debug:false) e


(* Symbolic parameters (jasmin2ec --model safety --safety-symbolic-params).
   In the functions [fc] such that [symbolic fc], every occurrence of a
   parameter in an expression is replaced by a phantom: a variable of global
   scope that no declaration defines, standing for the parameter.  The
   safety instrumentation and its final simplification (constant
   propagation, dead-code elimination) treat it as an initialised,
   never-assigned, unknown value, so they cannot evaluate the expressions
   that depend on parameters; the phantoms are replaced by the values of
   their parameters after the instrumentation ([remove_phantoms]).  The
   parameters keep their values in the size positions: types (sizes of
   arrays and sub-arrays) and the arguments of [is_arr_init], whose numeral
   bounds let the constant propagation record that an array is fully
   initialised. *)

(* Bottom-up rewriting of the expressions of a function by [f inside],
   where [inside] tells whether the expression is in a branch of a
   conditional whose condition satisfies [pcond] (the contracts are not). *)
let rec map_e f (e: pexpr) : pexpr =
  let r = map_e f in
  let e =
    match e with
    | Pconst _ | Pbool _ | Parr_init _ | Pvar _ | Pis_var_init _ -> e
    | Pget (al, aa, ws, x, e) -> Pget (al, aa, ws, x, r e)
    | Psub (aa, ws, len, x, e) -> Psub (aa, ws, len, x, r e)
    | Pload (al, ws, e) -> Pload (al, ws, r e)
    | Papp1 (o, e) -> Papp1 (o, r e)
    | Papp2 (o, e1, e2) -> Papp2 (o, r e1, r e2)
    | PappN (o, es) -> PappN (o, List.map r es)
    | Pif (ty, e, e1, e2) -> Pif (ty, r e, r e1, r e2)
    | Pbig (e, o, x, e1, e2, e0) -> Pbig (r e, o, x, r e1, r e2, r e0)
    | Pis_mem_init (e1, e2) -> Pis_mem_init (r e1, r e2) in
  f e

(* the array stores go through [f] as the corresponding loads *)
let map_lv f (lv: plval) : plval =
  match lv with
  | Lnone _ | Lvar _ -> lv
  | Lmem (al, ws, vi, e) -> Lmem (al, ws, vi, map_e f e)
  | Laset (al, aa, ws, x, e) ->
    begin match f (Pget (al, aa, ws, gkvar x, map_e f e)) with
    | Pget (_, _, _, _, e) -> Laset (al, aa, ws, x, e)
    | _ -> assert false end
  | Lasub (aa, ws, len, x, e) ->
    begin match f (Psub (aa, ws, len, gkvar x, map_e f e)) with
    | Psub (_, _, _, _, e) -> Lasub (aa, ws, len, x, e)
    | _ -> assert false end

let map_func pcond f fc =
  let rec instr inside i =
    let e = map_e (f inside) and lv = map_lv (f inside) and c = cmd inside in
    let i_desc =
      match i.i_desc with
      | Cassgn (x, tg, ty, e1) -> Cassgn (lv x, tg, ty, e e1)
      | Copn (xs, t, o, es) -> Copn (List.map lv xs, t, o, List.map e es)
      | Csyscall (xs, o, es) -> Csyscall (List.map lv xs, o, List.map e es)
      | Cassert (msg, e1) -> Cassert (msg, e e1)
      | Cif (b, c1, c2) ->
        let c' = cmd (inside || pcond b) in
        Cif (e b, c' c1, c' c2)
      | Cfor (x, (d, e1, e2), c1) -> Cfor (x, (d, e e1, e e2), c c1)
      | Cwhile (a, c1, b, loc, c2) -> Cwhile (a, c c1, e b, loc, c c2)
      | Ccall (xs, fn, es) -> Ccall (List.map lv xs, fn, List.map e es) in
    { i with i_desc }
  and cmd inside c = List.map (instr inside) c in
  let cond = List.map (fun (p, e) -> p, map_e (f false) e) in
  { fc with
    f_contra =
      Option.map (fun c -> { c with f_pre = cond c.f_pre; f_post = cond c.f_post })
        fc.f_contra;
    f_body = cmd false fc.f_body }

(* does [e] mention a variable of [vs]? *)
let rec mentions vs (e: pexpr) =
  let m = mentions vs in
  match e with
  | Pconst _ | Pbool _ | Parr_init _ -> false
  | Pvar x -> Spv.mem (L.unloc x.gv) vs
  | Pis_var_init x -> Spv.mem (L.unloc x) vs
  | Pget (_, _, _, x, e) | Psub (_, _, _, x, e) -> Spv.mem (L.unloc x.gv) vs || m e
  | Pload (_, _, e) | Papp1 (_, e) -> m e
  | Papp2 (_, e1, e2) | Pis_mem_init (e1, e2) -> m e1 || m e2
  | PappN (_, es) -> List.exists m es
  | Pif (_, e, e1, e2) -> m e || m e1 || m e2
  | Pbig (e, _, _, e1, e2, e0) -> m e || m e1 || m e2 || m e0

(* [symbolic_pre params value lit fc]: the rewritings of a symbolic function
   before the substitution of its parameters:
   - the arguments of is_arr_init get the values of the parameters ([value]);
   - in the branches of the conditionals whose condition depends on
     parameters, the literal offset of an access to an array, or of a
     sub-array, whose size depends on parameters becomes a phantom ([lit]).
     The bound check of such an access only involves numerals, and its truth
     may depend on the parameters (e.g. a slice of a buffer sized for the
     other branch, out of bounds exactly where the branch is dead): folded,
     it would be [false] at some points and dropped at the others. *)
let symbolic_pre params value lit fc =
  let pdep_ty ty =
    match ty with Arr (_, PE e) -> mentions params e | Bty _ -> false in
  let pdep x len =
    pdep_ty (L.unloc x.gv).v_ty || (match len with Some (PE e) -> mentions params e | None -> false) in
  let f inside e =
    match e with
    | PappN (Ois_arr_init _ as o, es) -> PappN (o, List.map (psubst_e value) es)
    | Pget (al, aa, ws, x, (Pconst _ as i)) when inside && pdep x None ->
      Pget (al, aa, ws, x, lit i)
    | Psub (aa, ws, len, x, (Pconst _ as i)) when inside && pdep x (Some len) ->
      Psub (aa, ws, len, x, lit i)
    | _ -> e in
  map_func (mentions params) f fc

(* The variable substitutions of a symbolic function: the parameters are
   mapped by [subst_val] (to their values) in the size positions and by
   [subst_sym] (to their phantoms) elsewhere; both rename the local variables
   in the same way. *)
let psubst_v_sym subst_val subst_sym =
  let locals = ref Mpv.empty in
  let rec aux subst v : pexpr =
    let k = v.gs in
    let v = v.gv in
    let v_ = v.L.pl_desc in
    let e =
      match Mpv.find_opt v_ subst with
      | Some e -> e
      | None when k = Expr.Sglob -> Pvar { gv = v; gs = k }  (* a phantom *)
      | None ->
        try Mpv.find v_ !locals
        with Not_found ->
          assert (not (PV.is_glob v_));
          let ty = psubst_ty (aux subst_val) v_.v_ty in
          let v' = PV.mk v_.v_name v_.v_kind ty v_.v_dloc v_.v_annot in
          let v = {v with L.pl_desc = v'} in
          let v = { gv = v; gs = k } in
          let e = Pvar v in
          locals := Mpv.add v_ e !locals;
          e in
    match e with
    | Pvar x ->
      let k = x.gs in
      let x = {x.gv with L.pl_loc = L.loc v} in
      let x = {gv = x; gs = k} in
      Pvar x
    | _      -> e in
  aux subst_val, aux subst_sym

(* With [symbolic], also returns the phantoms, with the values of their
   parameters; without, the substitution is the standard one. *)
let psubst_prog ?symbolic (prog:('info, 'asm) pprog) =
  let sym = match symbolic with Some _ -> true | None -> false in
  let subst = ref (Mpv.empty : pexpr Mpv.t) in
  (* with [symbolic]: [subst] with the parameters mapped to their phantoms *)
  let subst_sym = ref (Mpv.empty : pexpr Mpv.t) in
  let params = ref Spv.empty in
  let phantoms = ref [] in
  let rec aux = function
    | [] -> [], []
    | MIparam(v,e) :: items ->
        let g, p = aux items in
        let f = psubst_v !subst in
        let e = psubst_e f e in
        subst := Mpv.add v e !subst;
        if sym then begin
          let x = PV.mk v.v_name v.v_kind (psubst_ty f v.v_ty) v.v_dloc v.v_annot in
          params := Spv.add v !params;
          phantoms := (x, e) :: !phantoms;
          subst_sym := Mpv.add v (Pvar (gkglob (L.mk_loc v.v_dloc x))) !subst_sym
        end;
        g, p
    | MIglobal (v, e) :: items ->
      let g, p = aux items in
      let f = psubst_v !subst in
      let v' =
        let v =
          gsubst_gvar f {gv = L.mk_loc L._dummy v; gs = Expr.Sglob} in
        assert (not (is_gkvar v)); L.unloc v.gv in
      let e = psubst_ge f e in
      let gv = Pvar (gkglob (L.mk_loc L._dummy v')) in
      subst := Mpv.add v gv !subst;
      if sym then subst_sym := Mpv.add v gv !subst_sym;
      (v', e) :: g, p
    | MIfun fc :: items ->
        let g, p = aux items in
        let fc =
          match symbolic with
          | Some symbolic when symbolic fc ->
            (* the value of a parameter, as a numeral when it is an integer
               (as remove_phantoms prints it) *)
            let value v =
              let v_ = L.unloc v.gv in
              if Spv.mem v_ !params then
                let e = Mpv.find v_ !subst in
                try Pconst (int_of_expr e) with HiError _ -> e
              else Pvar v in
            let lit i =
              let x = PV.mk "lit" Const (Bty Int) fc.f_loc [] in
              phantoms := (x, i) :: !phantoms;
              Pvar (gkglob (L.mk_loc fc.f_loc x)) in
            let fc = symbolic_pre !params value lit fc in
            let f_val, f_sym = psubst_v_sym !subst !subst_sym in
            let subst_ty = psubst_ty f_val in
            let flen = psubst_e_ f_val in
            let dov v =
              L.unloc (gsubst_vdest f_sym (L.mk_loc L._dummy v)) in
            {
              fc with
              f_tyin = List.map subst_ty fc.f_tyin;
              f_contra = Option.bind fc.f_contra (gsubst_cf_contra flen f_sym);
              f_args = List.map dov fc.f_args;
              f_body = gsubst_c flen f_sym fc.f_body;
              f_tyout = List.map subst_ty fc.f_tyout;
              f_ret  = List.map (gsubst_vdest f_sym) fc.f_ret
            }
          | _ ->
            let subst_v = psubst_v !subst in
            let subst_ty = psubst_ty subst_v in
            let dov v =
              L.unloc (gsubst_vdest subst_v (L.mk_loc L._dummy v)) in
            let aux =
              gsubst_cf_contra (psubst_e_ subst_v) subst_v
            in
            {
              fc with
              f_tyin = List.map subst_ty fc.f_tyin;
              f_contra = Option.bind fc.f_contra aux;
              f_args = List.map dov fc.f_args;
              f_body = gsubst_c (psubst_e_ subst_v) subst_v fc.f_body;
              f_tyout = List.map subst_ty fc.f_tyout;
              f_ret  = List.map (gsubst_vdest subst_v) fc.f_ret
            } in
        g, fc::p in
    let g, p = aux prog in
    g, p, !phantoms

let isubst_len ?loc (PE e) =
  let z = int_of_expr ?loc e in
  try Z.to_int z
  with Z.Overflow ->
    hierror ?loc "cannot define a (sub-)array of size %a, this number is too big" Z.pp_print z

let isubst_ty ?loc = function
  | Bty ty -> Bty ty
  | Arr(ty, e) -> Arr(ty, isubst_len ?loc e)


let isubst_prog ?(phantoms = []) glob prog =

  let isubst_v subst =
    let aux v0 =
      let k = v0.gs in
      let v = v0.gv in
      let v_ = v.L.pl_desc in
      let e =
        try Mpv.find v_ !subst
        with Not_found ->
          let ty = isubst_ty ~loc:v_.v_dloc v_.v_ty in
          let v1 = V.mk v_.v_name v_.v_kind ty v_.v_dloc v_.v_annot in
          let v  = { v with L.pl_desc = v1 } in
          let v0 = { gv = v; gs = k } in
          let e = Pvar v0 in
          subst := Mpv.add v_ e !subst;
          e in
      match e with
      | Pvar x ->
        let k = x.gs in
        let x = {x.gv with L.pl_loc = L.loc v} in
        let x = {gv = x; gs = k} in
        Pvar x
      | _      -> e in
    aux in

  let subst : expr Mpv.t ref = ref Mpv.empty in

  let isubst_glob (x, gd) =
    let subst_v = isubst_v subst in
    let x =
      let x =
        gsubst_gvar subst_v {gv = L.mk_loc L._dummy x; gs = Expr.Sglob} in
      assert (not (is_gkvar x)); L.unloc x.gv in

    let gd =
      match gd with
      | GEword e -> GEword (gsubst_e isubst_len subst_v e)
      | GEarray es -> GEarray (List.map (gsubst_e isubst_len subst_v) es) in
    x, gd in
  let glob = List.map isubst_glob glob in

  (* the phantoms are shared by all functions, like the globals *)
  let phantoms =
    List.map (fun (x, e) ->
        let subst_v = isubst_v subst in
        let x = gsubst_gvar subst_v {gv = L.mk_loc x.v_dloc x; gs = Expr.Sglob} in
        L.unloc x.gv, gsubst_e isubst_len subst_v e)
      phantoms in

  let subst = !subst in

  let isubst_item fc =
    let subst = ref subst in
    let subst_v = isubst_v subst in
    let dov v =
      L.unloc (gsubst_vdest subst_v (L.mk_loc L._dummy v)) in
    (* Order matters so that the clearest error is triggered first.
       We use let-in to enforce the right order *)
    let f_args = List.map dov fc.f_args in
    let f_ret  = List.map (gsubst_vdest subst_v) fc.f_ret in
    let fc = {
        fc with
        f_tyin = List.map isubst_ty fc.f_tyin;
        f_contra =  Option.bind fc.f_contra (gsubst_cf_contra isubst_len subst_v);
        f_args;
        f_body = gsubst_c isubst_len subst_v fc.f_body;
        f_tyout = List.map isubst_ty fc.f_tyout;
        f_ret;
      } in
    fc
  in
  let isubst_item fc =
    try isubst_item fc
    with HiError e -> raise (HiError { e with err_funname = Some fc.f_name.fn_name })
  in

  let prog = List.map isubst_item prog in
  glob, prog, phantoms



(* ---------------------------------------------------------------- *)
(* Remove parameter from program definition                         *)

exception NotAConstantExpr

let in_range s sz i =
  if s = Wsize.Signed &&
     not (Z.lt i (Z.shift_left Z.one ((int_of_ws sz)/2))) then
     Z.sub i (Z.shift_left Z.one (int_of_ws sz))
  else i

let rec constant_of_expr (e: Prog.expr) : Z.t =
  let open Prog in

  match e with
  | Papp1 (Oword_of_int sz, e) ->
      clamp sz (constant_of_expr e)

  | Papp1(Oint_of_word(s, sz), e) ->
      let i = clamp sz (constant_of_expr e) in
      in_range s sz i

  | Pconst z ->
      z

  | _ -> raise NotAConstantExpr

let eval_globals globals =
  let global_tbl = Hv.create 101 in
  let add_glob x gv = Hv.add global_tbl x gv in
  let get_glob x = Hv.find_option global_tbl (Conv.var_of_cvar x) in

  let mk_word ws e =
    let open Constant_prop in
    let e = Conv.cexpr_of_expr e in
    let e = Wint_word.wi2w_e e in
    let c = const_prop_e (fun _ -> assert false) (Some get_glob) Var0.Mvar.empty e in
    let z = constant_of_expr (Conv.expr_of_cexpr c) in
    Word0.wrepr ws (Conv.cz_of_z (clamp ws z)) in


  let doglob (x, e) =
    let gv =
      match x.v_ty, e with
      | Bty (U ws), GEword e ->
        begin try Global.Gword (ws, mk_word ws e)
        with NotAConstantExpr ->
          hierror ~loc:x.v_dloc "the expression assigned to global variable %a must evaluate to a constant word"
            (Printer.pp_var ~debug:false) x
        end
      | Arr (_ws, n), GEarray es when List.length es <> n ->
         let m = List.length es in
         hierror ~loc:x.v_dloc "array size mismatch for global variable %a: %d %s given (%d expected)"
           (Printer.pp_var ~debug:false) x
           (List.length es)
           (if m > 1 then "values" else "value")
           n
      | Arr (ws, n), GEarray es ->
        let p = Conv.pos_of_int (n * size_of_ws ws) in
        let mk_word_i i e =
          try mk_word ws e
          with NotAConstantExpr ->
            hierror ~loc:x.v_dloc "in the list assigned to global variable %a, the expression at position %d must evaluate to a constant"
              (Printer.pp_var ~debug:false) x
              i
        in
        let t = Warray_.WArray.of_list ws (List.mapi mk_word_i es) in
        Global.Garr(p, t)
      | _, _ -> assert false in
    add_glob x gv;
    x, gv
  in
  List.rev_map doglob (List.rev globals)

let remove_params (prog : ('info, 'asm) pprog) =
  let globals, prog, _ = psubst_prog prog in
  let globals, prog, _ = isubst_prog globals prog in
  eval_globals globals, prog

let remove_params_symbolic ~symbolic (prog : ('info, 'asm) pprog) =
  let globals, prog, phantoms = psubst_prog ~symbolic prog in
  let globals, prog, phantoms = isubst_prog ~phantoms globals prog in
  (eval_globals globals, prog), phantoms

(* The phantoms are replaced by the values of their parameters, as numerals
   when they are integers (as the standard simplification would print them:
   the extraction of a library then does not depend on whether its
   parameters are defined by numerals or by expressions), and by their
   definitions otherwise (booleans, words). *)
let remove_phantoms (phantoms : (var * expr) list) ((globs, funcs) : ('info, 'asm) prog) =
  match phantoms with
  | [] -> globs, funcs
  | _ ->
    let rec value (e: expr) =
      match e with
      | Pconst z -> z
      | Papp1 (o, e1) -> int_of_op1 o (value e1)
      | Papp2 (o, e1, e2) -> int_of_op2 o (value e1) (value e2)
      | _ -> raise Not_found in
    let eval e = try Pconst (value e) with Not_found | HiError _ -> e in
    let tbl = Hv.create 17 in
    List.iter (fun (x, e) -> Hv.replace tbl x (eval e)) phantoms;
    let f v =
      if is_gkvar v then Pvar v
      else match Hv.find_option tbl (L.unloc v.gv) with
        | Some e -> e
        | None -> Pvar v in
    globs, List.map (gsubst_func (fun ?loc:_ len -> len) f) funcs


(* ---------------------------------------------------------------- *)
(* Rename all variable using fresh variable                         *)

let csubst_v () =
  let tbl = Hv.create 101 in
  let aux v =
    if not (is_gkvar v) then Pvar v
    else
      let v_ = v.gv.L.pl_desc in
      let v' =
        try Hv.find tbl v_
        with Not_found ->
          let v' = V.clone v_ in
          Hv.add tbl v_ v'; v' in
    Pvar (gkvar { v.gv with L.pl_desc = v' }) in
  aux

let clone_func fc =
  let subst_v = csubst_v () in
  gsubst_func (fun ?loc:_ ty -> ty) subst_v fc

(* ---------------------------------------------------------------- *)
(* extend instruction info                                          *)

let rec extend_iinfo_i pre i =
  let i_desc =
    match i.i_desc with
    | Cassgn _ | Copn _ | Csyscall _ | Ccall _ | Cassert _ -> i.i_desc
    | Cif(e,c1,c2) ->
      Cif(e, extend_iinfo_c pre c1, extend_iinfo_c pre c2)
    | Cfor(x,r,c) ->
      Cfor(x,r, extend_iinfo_c pre c)
    | Cwhile (a, c1, e, loc, c2) ->
      Cwhile(a, extend_iinfo_c pre c1, e, loc, extend_iinfo_c pre c2) in
  let {L.base_loc = ii; L.stack_loc = l} = i.i_loc in
  let i_loc = L.i_loc ii (l @ pre) in
  { i with i_desc; i_loc }

and extend_iinfo_c pre c = List.map (extend_iinfo_i pre) c

let extend_iinfo {L.base_loc = i; L.stack_loc = l} fd =
  { fd with f_body = extend_iinfo_c (i::l) fd.f_body }

(* ---------------------------------------------------------------- *)
(* Perform a substitution of variable by variable                   *)

type vsubst = var Mv.t

let vsubst_v s v = try Mv.find v s with Not_found -> v

let vsubst_vi s v = {v with L.pl_desc = vsubst_v s (L.unloc v) }

let vsubst_gv s v = { v with gv = vsubst_vi s v.gv }

let vsubst_ve s v = Pvar (vsubst_gv s v)

let vsubst_e  s = gsubst_e  (fun ?loc:_ ty -> ty) (vsubst_ve s)
let vsubst_es s = gsubst_es (fun ?loc:_ ty -> ty) (vsubst_ve s)

let vsubst_lval  s = gsubst_lval  (fun ?loc:_ ty -> ty) (vsubst_ve s)
let vsubst_lvals s = gsubst_lvals (fun ?loc:_ ty -> ty) (vsubst_ve s)

let vsubst_i s = gsubst_i (fun ?loc:_ ty -> ty) (vsubst_ve s)
let vsubst_c s = gsubst_c (fun ?loc:_ ty -> ty) (vsubst_ve s)

let vsubst_func s = gsubst_func (fun ?loc:_ ty -> ty) (vsubst_ve s)

