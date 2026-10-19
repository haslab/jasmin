type amodel =
  | ArrayOld
  | WArray
  | BArray

(* the functions whose auxiliary variables are never shared (see jasmin2ec
   --no-safety-simplify; only used by the safety model) *)
val fresh_aux_for : (Prog.funname -> bool) ref

val ty_expr : Prog.expr -> Prog.ty
val ty_lval : Prog.lval -> Prog.ty
val extract :
  ('info, ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op) Prog.prog ->
  Utils.architecture ->
  Wsize.wsize ->
  Wsize.wsize ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
  Utils.model ->
  amodel ->
  string list ->
  string option ->
  Format.formatter ->
  unit

val generate_safety_lemmas : string -> 
  ('info, ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op) Prog.prog ->
  Utils.architecture ->
  Wsize.wsize ->
  Wsize.wsize ->
  ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
  Utils.model ->
  amodel ->
  string list ->
  string option ->
  Format.formatter ->
  unit