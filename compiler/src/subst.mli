open Prog

(* apply a substitution within a function *)
val gsubst_func : (?loc:L.t -> 'ty1 -> 'ty2) -> ('ty1 ggvar -> 'ty2 gexpr) -> ('ty1, 'info, 'asm) gfunc -> ('ty2, 'info, 'asm) gfunc

(* apply a substitution within a function *)
val subst_func : ('ty gvar_i -> 'ty gexpr) -> ('ty, 'info, 'asm) gfunc -> ('ty, 'info, 'asm) gfunc

(* replace parameter by their definition everywhere in the program *)
val remove_params : ('info, 'asm) pprog -> ('info, 'asm) prog

(* [remove_params_symbolic ~symbolic p]: as [remove_params], except that in
   the functions [fc] such that [symbolic fc] the parameters are replaced, in
   the expressions outside of types and of the arguments of [is_arr_init], by
   phantoms (variables of global scope that no declaration defines); also
   returns the phantoms with the values of their parameters *)
val remove_params_symbolic :
  symbolic:((pexpr_, 'info, 'asm) gfunc -> bool) ->
  ('info, 'asm) pprog -> ('info, 'asm) prog * (var * expr) list

(* replace the phantoms of [remove_params_symbolic] by the values of their
   parameters *)
val remove_phantoms : (var * expr) list -> ('info, 'asm) prog -> ('info, 'asm) prog

(* rename all variable using fresh variables *)
val clone_func : ('info, 'asm) func -> ('info, 'asm) func

val extend_iinfo : L.i_loc -> ('info, 'asm) func -> ('info, 'asm) func
(* ---------------------------------------------------------------- *)
(* Perform a substitution of variable by variable                   *)

type vsubst = var Mv.t

val vsubst_v : vsubst -> var -> var

val vsubst_vi : vsubst -> var_i -> var_i

val vsubst_e  : vsubst -> expr  -> expr
val vsubst_es : vsubst -> exprs -> exprs

val vsubst_lval  : vsubst -> lval  -> lval
val vsubst_lvals : vsubst -> lvals -> lvals

val vsubst_i : vsubst -> ('info, 'asm) instr -> ('info, 'asm) instr
val vsubst_c : vsubst -> ('info, 'asm) stmt  -> ('info, 'asm) stmt

val vsubst_func : vsubst -> ('info, 'asm) func -> ('info, 'asm) func
