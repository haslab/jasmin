open Prog

let get_array_size (access: Warray_.arr_access) (arr: int gvar_i): int =
  match (L.unloc arr).v_ty with
    | Arr (ws, array_size) -> 
       ( match access with
          | AAdirect -> array_size
          | AAscale -> size_of_ws ws * array_size)
    | _ -> assert(false)

let create_assert (assertion_expr: int gexpr): (int, 'info, 'asm) ginstr =
  {
    i_desc = Cassert (Expr.Assert, Expr.Cas, assertion_expr);
    i_loc = L.i_dummy ;
    i_info = ();
    i_annot = [];
  }

let create_assert_access_array (a: Warray_.arr_access) (size:Wsize.wsize)  (arr: int gvar_i) (e: int gexpr): (int, 'info, 'asm) ginstr list =
    let array_size_expr =  get_array_size a arr in
    let index = 
      match a with
      | AAdirect -> e
      | AAscale ->  Papp2 (E.Omul E.Op_int, e, Pconst (Z.of_int(size_of_ws size)))
    in
    [
      create_assert(Papp2 (E.Oge E.Cmp_int, index, Pconst Z.zero));  
      create_assert(Papp2 (E.Olt E.Cmp_int, index, Pconst (Z.of_int(array_size_expr)))); 
    ]

let create_assert_subarray (access: Warray_.arr_access) (wsize:Wsize.wsize) (size:int) (arr: int gvar_i) (e: int gexpr): (int, 'info, 'asm) ginstr list =
    let array_size_expr = Pconst (Z.of_int(get_array_size access arr)) in
    let sub_arr_size = 
      match access with
      | AAdirect -> size
      | AAscale -> (size_of_ws wsize) * size
    in
    let index = 
      match access with
      | AAdirect ->  Papp2 (E.Oadd E.Op_int,e, Pconst (Z.of_int(sub_arr_size)))
      | AAscale -> 
        let size_scaled = Papp2 (E.Omul E.Op_int, e, Pconst (Z.of_int(size_of_ws wsize))) in
        Papp2 (E.Oadd E.Op_int, size_scaled, Pconst (Z.of_int(sub_arr_size)))
    in
    [
      create_assert(Papp2 (E.Oge E.Cmp_int, index, Pconst Z.zero));  
      create_assert(Papp2 (E.Olt E.Cmp_int, index, array_size_expr)); 
    ]


let rec get_asserts_expr (e: int gexpr) : (int, 'info, 'asm) ginstr list =
  match e with
  | Pconst _ -> []
  | Pbool _ -> []
  | Parr_init _ -> []
  | Pvar _ -> []
  | Pget (_,a,size,var,e1) -> 
    let asserts = create_assert_access_array a size var.gv e1 in
    asserts @ get_asserts_expr e1
  | Psub  (access, wsize,size,arr, e1) -> 
    let asserts = create_assert_subarray access wsize size arr.gv e1 in
    asserts @ get_asserts_expr e1
  | Pload (_,_,_,e1) -> get_asserts_expr e1 (*add memory logic*)
  | Papp1 (_, e1) -> get_asserts_expr e1
  | Papp2 (E.Odiv _, e1, denom) -> 
    let assertion_expr = Papp2 (E.Oneq E.Op_int, denom, Pconst Z.zero) in
    [create_assert assertion_expr] @  get_asserts_expr e1 @ get_asserts_expr denom
  | Papp2 (_, e1, e2) -> get_asserts_expr e1 @ get_asserts_expr e2
  | PappN (_, exprs) -> List.flatten (List.map (get_asserts_expr) exprs)
  | Pif (_, e1, e2, e3) -> 
      get_asserts_expr e1
      @ get_asserts_expr e2
      @ get_asserts_expr e3
  | _ -> []

let get_asserts_lval (lval: int glval) : (int, 'info, 'asm) ginstr list =
  match lval with
  | Lnone _ -> []
  | Lvar _ -> []
  | Lmem (_,_,_,e1) -> get_asserts_expr e1 (*add memory asserts*)
  | Laset (_,a,wsize,arr,e1) -> (create_assert_access_array a wsize arr e1) @ get_asserts_expr e1
  | Lasub (a,wsize,size,arr,e1) -> (create_assert_subarray a wsize size arr e1) @ get_asserts_expr e1

let rec add_asserts_function (instructions: (int, 'info, 'asm) ginstr list) : (int, 'info, 'asm) ginstr list =
  match instructions with
  | [] -> []
  | i :: rest ->
      let new_instrs =
        match i.i_desc with
        | Cassgn (lval, _, _, expr) -> 
          let asserts_lval = get_asserts_lval (lval) in
            let asserts = get_asserts_expr expr in
            asserts_lval @ asserts @ [i]
        | Cif (c,e1,e2) -> 
            let asserts = get_asserts_expr c in
            let new_e1 = add_asserts_function e1 in
            let new_e2 = add_asserts_function e2 in
            asserts @ [ { i with i_desc = Cif (c, new_e1, new_e2) } ]
        | Cfor (x, r, body) ->
            let new_body = add_asserts_function body in
            [ { i with i_desc = Cfor (x, r, new_body) } ]
        | Cwhile (a, body1, c, body2) ->
            let new_body1 = add_asserts_function body1 in
            let new_body2 = add_asserts_function body2 in
            let asserts = get_asserts_expr c in
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
