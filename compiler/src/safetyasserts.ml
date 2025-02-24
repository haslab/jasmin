open Prog
module E = Expr

module StringSet = Set.Make(String)


let valid_arr_abstract_pred = {
  E.pa_name = "valid_arr";
  E.pa_tyin = [Type.Coq_sint; Type.Coq_sword (U64); Type.Coq_sint];
  E.pa_tyout = Type.Coq_sbool; 
} 

let valid_mem_abstract_pred = {
  E.pa_name = "valid_mem";
  E.pa_tyin = [ Type.Coq_sword (U64); Type.Coq_sword (U64); Type.Coq_sint];
  E.pa_tyout = Type.Coq_sbool; 
}

let aligned_arr_abstract_pred = {
  E.pa_name = "aligned_arr";
  E.pa_tyin = [Type.Coq_sint;Type.Coq_sint];
  E.pa_tyout = Type.Coq_sbool; 
}

let aligned_mem_abstract_pred = {
  E.pa_name = "aligned_mem";
  E.pa_tyin = [Type.Coq_sint; Type.Coq_sword (U64); Type.Coq_sint];
  E.pa_tyout = Type.Coq_sbool; 
}

let init_var_abstract_pred = {
  E.pa_name = "init";
  E.pa_tyin = [Type.Coq_sbool];
  E.pa_tyout = Type.Coq_sbool; 
}

let init_arr_abstract_pred = {
  E.pa_name = "init_arr";
  E.pa_tyin = [Type.Coq_sbool; Type.Coq_sint; Type.Coq_sint];
  E.pa_tyout = Type.Coq_sbool; 
}

type safety_assert = 
 | Not_zero of expr
 | Valid_arr of var_i * expr * int
 | Valid_mem of var_i * expr * int
 | Aligned_arr  of int * expr        
 | Aligned_mem  of int * var_i * expr
 | Init of var_i             
 | Init_arr of var_i * expr * int            

let get_array_size (arr: var_i): int =
  match (L.unloc arr).v_ty with
    | Arr (ws, array_size) ->  size_of_ws ws * array_size
    | _ -> assert(false)

let create_assert (assertion_expr: expr): ('info, 'asm) instr =
  {
    i_desc = Cassert (Expr.Assert, Expr.Cas, assertion_expr);
    i_loc = L.i_dummy ;
    i_info = ();
    i_annot = [];
  }


let safety_assert_to_cassert( a:safety_assert): ('info, 'asm) instr =
  let assert_expr = 
    match a with
      | Not_zero (expr) ->
        Papp2 (E.Oneq E.Op_int, expr, Pconst Z.zero)
      | Valid_arr (arr,offset,size) ->
        let arr_size = Pconst (Z.of_int(get_array_size arr)) in
        let var_size = Pconst (Z.of_int((size))) in
        PappN(Oabstract valid_arr_abstract_pred,[arr_size;offset;var_size])
      | Valid_mem (ptr,offset,size) ->
        let var_size = Pconst (Z.of_int((size))) in
        let ptr_var = {
          gv  = ptr;
          gs  = E.Slocal;
        } in
        PappN(Oabstract valid_mem_abstract_pred,[Pvar(ptr_var);offset;var_size]) 
      | Aligned_arr (size,expr) ->
        let var_size = Pconst (Z.of_int((size))) in
        PappN(Oabstract aligned_arr_abstract_pred,[var_size;expr])
      | Aligned_mem (size,ptr,expr) ->
        let var_size = Pconst (Z.of_int((size))) in
        let ptr_var = {
          gv  = ptr;
          gs  = E.Slocal;
        } in
        PappN(Oabstract aligned_mem_abstract_pred,[var_size;Pvar(ptr_var);expr])
      | Init (var) ->
        let var = {
          gv  = var;
          gs  = E.Slocal;
        } in
        PappN(Oabstract init_var_abstract_pred,[Pvar(var)])
      | Init_arr (var,expr,size) ->
        let var = {
          gv  = var;
          gs  = E.Slocal;
        } in
        let size = Pconst (Z.of_int((size))) in
        PappN(Oabstract init_arr_abstract_pred,[Pvar(var);expr;size])
  in
  create_assert(assert_expr)






let create_assert_access_array (a: Warray_.arr_access) (size:Wsize.wsize)  (arr: var_i) (e: expr): safety_assert =
    let index = 
      match a with
      | AAdirect -> e
      | AAscale ->  Papp2 (E.Omul E.Op_int, e, Pconst (Z.of_int(size_of_ws size)))
    in
    Valid_arr (arr, index, size_of_ws size)

let create_assert_subarray (access: Warray_.arr_access) (wsize:Wsize.wsize) (size:int) (arr: var_i) (e: expr): safety_assert =
    let sub_arr_size = 
      match access with
      | AAdirect -> size
      | AAscale -> (size_of_ws wsize) * size 
    in
    let index = 
      match access with
      | AAdirect -> e
      | AAscale ->  Papp2 (E.Omul E.Op_int, e, Pconst (Z.of_int(size_of_ws wsize)))
    in

    Valid_arr (arr, index, sub_arr_size)

let create_assert_memory_access (wsize:Wsize.wsize) (var:var_i) (e: expr): safety_assert =
  Valid_mem(var,e,(size_of_ws wsize))


let create_assert_alignment_array (access: Warray_.arr_access) (wsize:Wsize.wsize) (e:expr): safety_assert =
  let index = 
    match access with
    | AAdirect -> e
    | AAscale ->  Papp2 (E.Omul E.Op_int, e, Pconst (Z.of_int(size_of_ws wsize)))
  in
  Aligned_arr(size_of_ws wsize,index)

let create_assert_alignment_mem (wsize:Wsize.wsize) (ptr: var_i) (e:expr): safety_assert =
  let offset = Papp2 (E.Omul E.Op_int, e, Pconst (Z.of_int(size_of_ws wsize))) in
  Aligned_mem(size_of_ws wsize,ptr,offset)

let rec get_asserts_expr (e: expr) (init_vars: StringSet.t) : safety_assert list =
  match e with
  | Pconst _ | Pbool _ | Parr_init _ -> []
  | Pvar v ->
      let var_name = (L.unloc v.gv).v_name in
      if StringSet.mem var_name init_vars then [] else [Init v.gv]
  | Pget (align,a,size,var,e1) -> 
      let oob_assert = create_assert_access_array a size var.gv e1 in
      let arr_name = (L.unloc var.gv).v_name in
      let init_assert = if StringSet.mem arr_name init_vars then [] else [Init_arr (var.gv, e1, size_of_ws size)] in
      oob_assert :: init_assert @ get_asserts_expr e1 init_vars
  | Psub (access, wsize, size, arr, e1) -> 
      let safety_assert = create_assert_subarray access wsize size arr.gv e1 in
      safety_assert :: get_asserts_expr e1 init_vars
  | Pload (align,size,var,e1) -> 
      let safety_assert = create_assert_memory_access size var e1 in
      safety_assert :: get_asserts_expr e1 init_vars
  | Papp1 (_, e1) -> get_asserts_expr e1 init_vars
  | Papp2 (E.Odiv _, e1, denom) -> 
      let asserts_e1 = get_asserts_expr e1 init_vars in
      let asserts_denom = get_asserts_expr denom init_vars in
      Not_zero denom :: asserts_e1 @ asserts_denom
  | Papp2 (_, e1, e2) -> 
      let asserts_e1 = get_asserts_expr e1 init_vars in
      let asserts_e2 = get_asserts_expr e2 init_vars in
      asserts_e1 @ asserts_e2
  | PappN (_, exprs) -> 
      List.flatten(List.map (fun e -> get_asserts_expr e init_vars) exprs)
  | _ -> []

let get_asserts_lval (lval: lval) (init_vars: StringSet.t) : (safety_assert list * StringSet.t) =
  match lval with
  | Lnone _ -> ([], init_vars)
  | Lvar var ->
    let var_name = (L.unloc var).v_name in
    let new_init_vars = StringSet.add var_name init_vars in
    ([], new_init_vars)
  | Lmem (align, size, var, e1) -> 
    let safety_assert = create_assert_memory_access size var e1 in
    let asserts = get_asserts_expr e1 init_vars in
    (match align with
      | Aligned -> 
        let alignment_assert = create_assert_alignment_mem size var e1 in
        ([safety_assert;alignment_assert] @ asserts, init_vars)
      | Unaligned -> ([safety_assert] @ asserts,init_vars)
    )
  | Laset (align,a,wsize,arr,e1) -> 
    let oob_assert = create_assert_access_array a wsize arr e1 in
     let asserts = get_asserts_expr e1 init_vars in
    (match align with
      | Aligned -> 
        let alignment_assert = create_assert_alignment_array a wsize e1 in
        ([oob_assert;alignment_assert] @ asserts,init_vars)
      | Unaligned -> ([oob_assert] @ asserts,init_vars)
    )
  | Lasub (a,wsize,size,arr,e1) ->
     let asserts = get_asserts_expr e1 init_vars in
    ([create_assert_subarray a wsize size arr e1] @ asserts, init_vars)



let rec add_asserts_function (instructions: (int, 'info, 'asm) ginstr list) (init_vars: StringSet.t) : ((int, 'info, 'asm) ginstr list * StringSet.t) =
  match instructions with
  | [] -> ([], init_vars)
  | i :: rest ->
      let (new_instrs, new_init_vars) =
        match i.i_desc with
        | Cassgn (lval, _, _, expr) -> 
            let (asserts_lval, init_vars1) = get_asserts_lval lval init_vars in
            let asserts_expr = get_asserts_expr expr init_vars in
            let asserts = List.map safety_assert_to_cassert (asserts_lval @ asserts_expr) in
            (asserts @ [i], init_vars1)
        | Copn (lvals,_,_,exprs)
        | Csyscall (lvals,_,exprs)
        | Ccall (lvals,_,exprs)  -> 
            let (asserts_lvals, init_vars1) = List.fold_left (fun (acc_asserts, acc_vars) lval ->
              let (lval_asserts, new_vars) = get_asserts_lval lval acc_vars in
              (acc_asserts @ lval_asserts, new_vars)
            ) ([], init_vars) lvals in
            let asserts_exprs = List.flatten (List.map (fun e -> get_asserts_expr e init_vars) exprs) in
            let asserts = List.map safety_assert_to_cassert (asserts_lvals @ asserts_exprs) in
            (asserts @ [i], init_vars1)
        | Cif (c,e1,e2) -> 
            let asserts =  List.map safety_assert_to_cassert (get_asserts_expr c init_vars) in
            let (new_e1,init_vars1) = add_asserts_function e1 init_vars in
            let (new_e2,init_vars2) = add_asserts_function e2 init_vars in
            (asserts @ [ { i with i_desc = Cif (c, new_e1, new_e2) } ], StringSet.inter init_vars1 init_vars2)
        | Cfor (x, r, body) ->
          let dir,e1,e2 = r in
          if (e1<e2 && dir = Expr.DownTo) || (e1>e2 && dir = Expr.UpTo) then
            ([i],init_vars)
          else
            let var_name = (L.unloc x).v_name in
            let init_vars_for = StringSet.add var_name init_vars in
            let new_body,new_init_vars = add_asserts_function body init_vars_for in
            let asserts_exprs = get_asserts_expr e1 init_vars @ get_asserts_expr e2 init_vars in
            let asserts =  List.map safety_assert_to_cassert asserts_exprs in
            let new_init_vars = StringSet.remove var_name new_init_vars in
            (asserts @ [ { i with i_desc = Cfor (x, r, new_body) } ],new_init_vars)
        | Cwhile (a, body1, c, body2) ->
            let new_body1,new_init_vars = add_asserts_function body1 init_vars in
            let new_body2,_ = add_asserts_function body2 new_init_vars in
            let asserts = List.map safety_assert_to_cassert (get_asserts_expr c new_init_vars) in
            (asserts @ [ { i with i_desc = Cwhile (a, new_body1, c, new_body2) } ],new_init_vars)
        | _ -> ([i], init_vars) 
      in
      let (rest_instrs, final_vars) = add_asserts_function rest new_init_vars in
      (new_instrs @ rest_instrs, final_vars)

let add_asserts (prog: (unit, 'asm) prog): (unit, 'asm) prog =
  match prog with
  | (globals, funcs) -> 
      let updated_funcs =
        List.map (fun f ->
          let init_vars = List.fold_left (fun acc v -> StringSet.add v.v_name acc) StringSet.empty f.f_args in
          let updated_body, _ = add_asserts_function f.f_body init_vars in
          { f with f_body = updated_body }
        ) funcs
      in
      (globals, updated_funcs)
  