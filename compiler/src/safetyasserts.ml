open Prog


type safety_assert = 
 | Not_zero of expr
 | Valid_arr of var_i * expr * int
 | Valid_mem of var_i * expr * int
 | Aligned_arr  of int * expr        
 | Aligned_mem  of int * var_i * expr               

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
  match a with
    | Not_zero (expr) ->
      let dif_zero_expr = Papp2 (E.Oneq E.Op_int, expr, Pconst Z.zero) in
      create_assert(dif_zero_expr)
    | Valid_arr (arr,offset,size) ->
      let op_valid_arr = {
        name = "valid_arr";
        tyin = [Bty Int; Bty (U U64); Bty Int];
        tyout = Bty Bool; 
      } in
      let arr_size = Pconst (Z.of_int(get_array_size arr)) in
      let var_size = Pconst (Z.of_int((size))) in

      let valid_arr_expr = Pabstract(op_valid_arr,[arr_size;offset;var_size]) in
      create_assert(valid_arr_expr)
    | Valid_mem (ptr,offset,size) ->
      let op_valid_mem = {
        name = "valid_mem";
        tyin = [ Bty (U U64); Bty (U U64); Bty Int];
        tyout = Bty Bool; 
      } in
      let var_size = Pconst (Z.of_int((size))) in
      let valid_mem_expr = Pabstract(op_valid_mem,[Pfvar(ptr);offset;var_size]) in
      create_assert(valid_mem_expr)
    | Aligned_arr (size,expr) ->
      let op_aligned_mem = {
        name = "aligned_arr";
        tyin = [Bty Int;Bty Int];
        tyout = Bty Bool; 
      } in
      let var_size = Pconst (Z.of_int((size))) in
      let aligned_arr_expr = Pabstract(op_aligned_mem,[var_size;expr]) in
      create_assert(aligned_arr_expr)
    | Aligned_mem (size,ptr,expr) ->
      let op_aligned_mem = {
        name = "aligned_mem";
        tyin = [Bty Int; Bty (U U64); Bty Int];
        tyout = Bty Bool; 
      } in
      let var_size = Pconst (Z.of_int((size))) in
      let aligned_mem_expr = Pabstract(op_aligned_mem,[var_size;Pfvar(ptr);expr]) in
      create_assert(aligned_mem_expr)





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
      | AAscale -> (size_of_ws wsize) * size (*TEST*)
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

let rec get_asserts_expr (e: expr) : safety_assert list =
  match e with
  | Pconst _ -> []
  | Pbool _ -> []
  | Parr_init _ -> []
  | Pvar _ -> []
  | Pget (align,a,size,var,e1) -> 
    let oob_assert = create_assert_access_array a size var.gv e1 in
    (match align with
      | Aligned -> 
        let alignment_assert = create_assert_alignment_array a size e1 in
        [oob_assert;alignment_assert] @ get_asserts_expr e1
      | Unaligned -> [oob_assert] @ get_asserts_expr e1
    )    
  | Psub  (access, wsize,size,arr, e1) -> 
    let safety_assert = create_assert_subarray access wsize size arr.gv e1 in
    [safety_assert] @ get_asserts_expr e1
  | Pload (align,size,var,e1) -> 
    let safety_assert = create_assert_memory_access size var e1  in
    (match align with
      | Aligned -> 
      let alignment_assert = create_assert_alignment_mem size var e1 in
      [safety_assert;alignment_assert] @ get_asserts_expr e1
      | Unaligned -> [safety_assert] @ get_asserts_expr e1
    ) 
  | Papp1 (_, e1) -> get_asserts_expr e1
  | Papp2 (E.Odiv _, e1, denom) -> 
    let assert_div_zero = Not_zero (denom) in
    [assert_div_zero] @  get_asserts_expr e1 @ get_asserts_expr denom
  | Papp2 (_, e1, e2) -> get_asserts_expr e1 @ get_asserts_expr e2
  | PappN (_, exprs) -> List.flatten (List.map (get_asserts_expr) exprs)
  | Pif (_, e1, e2, e3) -> 
      get_asserts_expr e1
      @ get_asserts_expr e2
      @ get_asserts_expr e3
  | _ -> []

let get_asserts_lval (lval: lval) : safety_assert list =
  match lval with
  | Lnone _ -> []
  | Lvar _ -> []
  | Lmem (align,size,var,e1) -> 
    let safety_assert = create_assert_memory_access size var e1 in
    (match align with
      | Aligned -> 
        let alignment_assert = create_assert_alignment_mem size var e1 in
        [safety_assert;alignment_assert] @ get_asserts_expr e1
      | Unaligned -> [safety_assert] @ get_asserts_expr e1
    )
  | Laset (align,a,wsize,arr,e1) -> 
    let oob_assert = create_assert_access_array a wsize arr e1 in
    (match align with
      | Aligned -> 
        let alignment_assert = create_assert_alignment_array a wsize e1 in
        [oob_assert;alignment_assert] @ get_asserts_expr e1
      | Unaligned -> [oob_assert] @ get_asserts_expr e1
    )
  | Lasub (a,wsize,size,arr,e1) -> [create_assert_subarray a wsize size arr e1] @ get_asserts_expr e1

let rec add_asserts_function (instructions: (int, 'info, 'asm) ginstr list) : (int, 'info, 'asm) ginstr list =
  match instructions with
  | [] -> []
  | i :: rest ->
      let new_instrs =
        match i.i_desc with
        | Cassgn (lval, _, _, expr) -> 
            let asserts_lval = get_asserts_lval (lval) in
            let asserts_expr = get_asserts_expr expr in
            let asserts = List.map safety_assert_to_cassert (asserts_lval @ asserts_expr) in
            asserts @ [i]
        | Copn (lvals,_,_,exprs)
        | Csyscall (lvals,_,exprs)
        | Ccall (lvals,_,exprs)  -> 
            let asserts_lvals = List.flatten (List.map get_asserts_lval lvals) in
            let asserts_exprs = List.flatten (List.map get_asserts_expr exprs) in
            let asserts = List.map safety_assert_to_cassert (asserts_lvals @ asserts_exprs) in
            asserts @ [i]
        | Cif (c,e1,e2) -> 
            let asserts =  List.map safety_assert_to_cassert (get_asserts_expr c) in
            let new_e1 = add_asserts_function e1 in
            let new_e2 = add_asserts_function e2 in
            asserts @ [ { i with i_desc = Cif (c, new_e1, new_e2) } ]
        | Cfor (x, r, body) ->
            let new_body = add_asserts_function body in
            let _,e1,e2 = r in
            let asserts_exprs = get_asserts_expr e1 @ get_asserts_expr e2 in
            let asserts =  List.map safety_assert_to_cassert asserts_exprs in
            asserts @ [ { i with i_desc = Cfor (x, r, new_body) } ]
        | Cwhile (a, body1, c, body2) ->
            let new_body1 = add_asserts_function body1 in
            let new_body2 = add_asserts_function body2 in
            let asserts = List.map safety_assert_to_cassert (get_asserts_expr c) in
            asserts @ [ { i with i_desc = Cwhile (a, new_body1, c, new_body2) } ] 
        | _ -> [i] 
      in
      new_instrs @ add_asserts_function rest


let add_asserts (prog: (unit, 'asm) prog): (unit, 'asm) prog =
  match prog with
  | (globals, funcs) -> 
      let updated_funcs =
        List.map (fun f ->
          let updated_body = add_asserts_function (f.f_body) in
          { f with f_body = updated_body }
        ) funcs
      in
      (globals, updated_funcs)
