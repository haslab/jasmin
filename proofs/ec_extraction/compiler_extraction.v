Require Import
compiler
psem
safety
insert_cast
wint_int
extra_vars_call
contracts_asserts
remove_init_preds.


Section SAFETY_ASSERTS.
Context `{asmop:asmOp} {pd: PointerData} {msfsz : MSFsize}.
Context (create_var : v_kind -> string -> atype -> var_info -> var).
Context (B : var -> var).
Context {fcp : FlagCombinationParams}.
Context (is_move_op : asm_op_t -> bool).
Context (print_uprog : string -> _uprog -> _uprog).

(* The final constant propagation and dead-code elimination are only applied
   to the functions [fn] such that [simplify_fn fn] (by default, all of them).
   The other functions are returned as instrumented: every safety assertion is
   kept, including the statically true ones, and expressions and branches that
   only depend on compile-time values (e.g. [param] declarations) are left
   unevaluated.  The shape of their extraction then does not depend on the
   values of the parameters, which is what parametric safety proofs need (the
   OCaml caller also puts their shadow-array initialisations in a
   size-independent order and renumbers their variables, see
   Compile.create_safety_asserts).  Both passes are intraprocedural, so a
   selected function is simplified exactly as when all of them are, e.g. as in
   the extraction of a library whose safety models are reused. *)
Definition create_safety_asserts (simplify_fn: funname -> bool) (p: _uprog): result compiler_util.pp_error_loc _uprog :=
  (* First add the safety conditions *)
  let p := insert_cast_prog p in
  let p := print_uprog "insert cast " p in
  Let p := sc_prog p in
  let p := print_uprog "safety assert" p in
  (* This make the arguments and destinations of function call uniq variable.
     Similar to make reference argument *)
  Let p := extra_vars_call_prog create_var p in
  let p := print_uprog "extra vars call" p in
  (* Introduce the boolean variables that encode is_var_init and is_arr_init *)
  let p := rm_var_init_prog B p in
  let p := print_uprog "var init" p in
  (* Add the post after the call.
     Do we really want to keep it or to intergrate it into constant_prop ?
     One advantage is that static analysis can reuse the result more easyly ?
  *)
  let p := contracts_asserts_prog p in
  let p := print_uprog "contracts asserts" p in
  (* Performs constant propagation (on the functions selected by [simplify_fn]) *)
  let p := rm_var_init_const_prop_fn B simplify_fn p in
  let p := print_uprog "constant prop" p in
  (* Dead code (same functions) *)
  let p := rm_var_init_dc_fn is_move_op simplify_fn p in
  let p := print_uprog "rm var init" p in
  ok p
.

End SAFETY_ASSERTS.
