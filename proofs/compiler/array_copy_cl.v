From mathcomp Require Import all_ssreflect.
Require Import expr compiler_util.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
semantics: Ccopy x ws n y

x & y have type array(ws * n)
all y[i] is init (ok u)

*)

Module Import E.
  Definition pass : string := "array copy cl".

  Definition error := pp_internal_error_s pass "fresh variables are not fresh ...". 

End E.

Section Section.

Context `{asmop:asmOp}.
Context (fresh_counter: Ident.ident).

(*
  x = ArrayInit();
  for i = 0 to n {
    x[i] = y[i];
  }
*)

Definition add e ei := 
  match e with
  | Some e => Papp2 (Oadd Op_int) e ei
  | None   => ei 
  end.

Definition array_copy ii (x: var_i * option pexpr) (ws: wsize) (n: positive) (y: gvar * option pexpr) :=
  let '(x,ex) := x in
  let '(y,ey) := y in
  let i_name := fresh_counter in
  let i := {| v_var := {| vtype := sint ; vname := i_name |}; v_info := v_info x |} in
  let ei := Pvar (mk_lvar i) in
  let xei := add ex ei in
  let yei := add ey ei in
  let sz := Z.to_pos (wsize_size ws * n) in
  let pre := 
    if eq_gvar (mk_lvar x) y then Copn [::] AT_none sopn_nop [::]
    else Cassgn (Lvar x) AT_none (sarr sz) (Parr_init sz) in
  [:: MkI ii pre;
      MkI ii 
        (Cfor i (UpTo, Pconst 0, Pconst n) 
           [:: MkI ii (Cassgn (Laset Aligned AAscale ws x xei) AT_none (sword ws) (Pget Aligned AAscale ws y yei))])
    ].

Definition array_copy_c (array_copy_i : instr -> cexec cmd) (c:cmd) : cexec cmd := 
  Let cs := mapM array_copy_i c in 
  ok (flatten cs).

Definition is_copy o := 
  match o with 
  |  Opseudo_op (pseudo_operator.Ocopy ws p) => Some (ws, p) 
  | _ => None 
  end.

Definition is_Pvar es := 
  match es with 
  | [:: Pvar x] => Some (x, None)
  | [:: Psub AAscale ws n x e] => Some(x, Some(ws, n, e))
  | _ => None
  end.

Definition is_Lvar xs := 
  match xs with 
  | [:: Lvar x] => Some (x, None) 
  | [:: Lasub AAscale ws n x e] => Some (x, Some (ws, n, e))
  | _ => None
  end.

Definition check_x (A:Type) ii ws (xe: A * option (wsize * positive * pexpr)) := 
  match xe with
  | (x, None) => 
    ok (x, None)
  | (x, Some (ws', n', e)) => 
    Let _ := assert (ws' == ws) 
                    (pp_internal_error_s_at E.pass ii "bad type for copy") in
    ok (x, Some e)                    
  end.
                  
Fixpoint array_copy_i (i:instr) : cexec cmd := 
  let:(MkI ii id) := i in
  match id with
  | Cassgn _ _ _ _ => ok [:: i] 
  | Copn xs _ o es => 
    match is_copy o with
    | Some (ws, n) => 
      match is_Pvar es with
      | Some y =>
        match is_Lvar xs with
        | Some x => 
          Let x := check_x ii ws x in
          Let y := check_x ii ws y in  
          ok (array_copy ii x ws n y)
        | None => 
          (* FIXME error msg *)
          Error (pp_internal_error_s_at E.pass ii "copy destination is not a var")
        end 
      | None => 
        (* FIXME error msg *)
        Error (pp_internal_error_s_at E.pass ii "copy source is not a var")
      end
    | _ => ok [:: i] 
    end
  | Csyscall _ _ _ => ok [:: i]
  | Cassert _ _ _ => ok [:: i]
  | Cif e c1 c2    => 
      Let c1 := array_copy_c array_copy_i c1 in
      Let c2 := array_copy_c array_copy_i c2 in
      ok [:: MkI ii (Cif e c1 c2)]
  | Cfor i r c => 
      Let c := array_copy_c array_copy_i c in
      ok [:: MkI ii (Cfor i r c)]
  | Cwhile a c1 e c2 => 
      Let c1 := array_copy_c array_copy_i c1 in
      Let c2 := array_copy_c array_copy_i c2 in
      ok [:: MkI ii (Cwhile a c1 e c2)]
  | Ccall _ _ _ => ok [:: i]
  end.

Context {pT:progT}.

Definition array_copy_fd (f:fundef) :=
  let 'MkFun fi ci tyin params c tyout res ev := f in
  Let c := array_copy_c array_copy_i c in
  ok (MkFun fi ci tyin params c tyout res ev).

Definition array_copy_prog (p:prog) := 
  let V := vars_p (p_funcs p) in 
  Let _ := 
    assert (~~ Sv.mem {| vtype := sint ; vname := fresh_counter |} V) E.error 
  in
  Let fds := map_cfprog array_copy_fd (p_funcs p) in
  ok {| p_funcs := fds;
        p_globs := p_globs p;
        p_extra := p_extra p|}.

End Section.


