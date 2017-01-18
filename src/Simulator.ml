(* Defining the simulator *)

open Core_kernel.Std
open Abbrevs
open Util
open Expressions
open Attacker
open Z2Poly

(* ** Simulator functions *)

type simulator_term =
  | Const of int * (int list) list  (* constant id  *  constant dependent terms *)
  | Var   of int * (int list) list  (* variable id  *  variable dependent terms *)

let pp_inner_list _ list = F.printf "[%a]" (pp_list "," pp_int) list

let pp_simulator_term _ = function
  | Const (i, idxs) -> F.printf "Const(%d,%a)" i (pp_list "," pp_inner_list) idxs
  | Var   (i, idxs) -> F.printf "Var(%d,%a)" i (pp_list "," pp_inner_list) idxs

let expressions_to_simulator_terms expressions =
  let rec aux id_map id_counter converted = function
    | [] -> id_map, id_counter, converted
    | e :: rest ->
       let xor_list = expr_to_xor_list e in
       let (id_map, id_counter, new_expr) =
         L.fold_left xor_list 
             ~init:(id_map, id_counter, [])
             ~f:(fun (id_map, id_counter, terms) non_xor_term ->
               let f_search = fun (_,(e,_)) -> equal_expr e non_xor_term in
               begin match non_xor_term with
               | F(expr, _) ->
                  let id_map, id_counter, _ = aux id_map id_counter [] [expr] in
                  let find_map_index e =
                    let (i,_) = L.find_exn (Map.to_alist id_map) ~f:(fun (_,(e',_)) -> equal_expr e' e) in
                    i
                  in
                  begin match L.find (Map.to_alist id_map) ~f:f_search with
                  | Some (i,(_,idxs)) -> (id_map, id_counter, terms @ [Var(i,idxs)])
                  | None ->
                     let idxs = L.map (expr_to_xor_list expr) ~f:find_map_index in
                     let id_map = Map.add id_map ~key:id_counter ~data:(non_xor_term, [idxs]) in
                     (id_map, id_counter+1, terms @ [Var(id_counter, [idxs])])
                  end
               | Leaf(_) | VAR(_)->
                  begin match L.find (Map.to_alist id_map) ~f:f_search with
                  | Some (i,(_,idxs)) -> (id_map, id_counter, terms @ [Const(i,idxs)])
                  | None ->
                     let id_map = Map.add id_map ~key:id_counter ~data:(non_xor_term, [[id_counter]]) in
                     (id_map, id_counter+1, terms @ [Const(id_counter, [[id_counter]])])
                  end
               | Rand(_, exprs) ->
                  let id_map, id_counter, _ = aux id_map id_counter [] exprs in
                  let find_map_index e =
                    let (i,_) = L.find_exn (Map.to_alist id_map) ~f:(fun (_,(e',_)) -> equal_expr e' e) in
                    i
                  in
                  begin match L.find (Map.to_alist id_map) ~f:f_search with
                  | Some (i,(_,idxs)) -> (id_map, id_counter, terms @ [Const(i,idxs)])
                  | None ->
                     let idxs =
                       L.map exprs ~f:(fun e -> L.map (expr_to_xor_list e) ~f:find_map_index )
                     in
                     let id_map = Map.add id_map ~key:id_counter ~data:(non_xor_term, idxs) in
                     (id_map, id_counter+1, terms @ [Const(id_counter, idxs)])
                  end
               | Zero -> (id_map, id_counter, terms)
               | XOR(_,_) -> assert false
               end
             )
       in
       aux id_map id_counter (converted @ [new_expr]) rest
  in
  aux Int.Map.empty 0 [] expressions

let xor_gaussian_elimination (matrix : int list list) (vector : expression list) =
  (* This function solves the system matrix*x = vector,
     where matrix and vector have coefficients in {0,1}
     summation is defined as xor and multiplication as
     0*v = \vec{0} and 1*v = v for every vector v
   *)
  let sum_rows row1 row2 v1 v2 =
    L.map2_exn row1 row2 ~f:(fun a1 a2 -> if a1 = a2 then 0 else 1), simplify_expr (XOR(v1, v2))
  in
  let m = L.length matrix in
  let n = L.length (L.hd_exn matrix) in
  let search_for_non_zero non_used_rows col matrix =
    let rec aux = function
      | [] -> None
      | row :: rest_rows ->
         let el = L.nth_exn (L.nth_exn matrix row) col in
         if el = 0 then aux rest_rows
         else Some row
    in
    aux non_used_rows
  in
  let reduce_by_pivot row col matrix vector =
    let relevant_row = L.nth_exn matrix row in
    let relevant_v = L.nth_exn vector row in
    L.map (range 0 m)
      ~f:(fun k ->
        if k = row then relevant_row, relevant_v
        else
          let this_row = L.nth_exn matrix k in
          let this_v = L.nth_exn vector k in
          if L.nth_exn this_row col = 0 then this_row, this_v
          else sum_rows this_row relevant_row this_v relevant_v
      )
    |> L.unzip
  in
  let rec go reduced col_pivots vector col non_used_rows =
    if col >= n then reduced, col_pivots, vector
    else
      (* We search for a non-zero in column col and a non-used row *)
      match search_for_non_zero non_used_rows col reduced with
      | None -> go reduced col_pivots vector (col+1) non_used_rows
      | Some row ->
         let reduced, vector = reduce_by_pivot row col reduced vector in
         go reduced (col_pivots @ [col]) vector (col+1) (L.filter non_used_rows ~f:(fun r -> r <> row))
  in
  go matrix [] vector 0 (range 0 m)

let has_solution matrix vector =
  let reduced, _, vector = xor_gaussian_elimination matrix vector in
  let rec aux f_matrix f_vector = function
    | [], [] -> Some (f_matrix, f_vector)
    | row :: rest_rows, v :: rest_vector ->
       if not (L.exists row ~f:(fun a -> a = 1)) then
         if not (equal_expr v Zero) then None
         else aux f_matrix f_vector (rest_rows, rest_vector)
       else aux (f_matrix @ [row]) (f_vector @ [v]) (rest_rows, rest_vector)
    | _ -> assert false
  in
  aux [] [] (reduced, vector)

let rec can_be_generated expression known_terms =
  let expression = simplify_expr expression in
  let known_terms = L.map known_terms ~f:simplify_expr in
  let xor_atoms =
    (expr_to_xor_list expression) @ (L.concat (L.map known_terms ~f:expr_to_xor_list ))
    |> L.dedup ~compare:compare_expr
  in

  (* We are allowed also to call the random oracles *)

  let random_oracle_terms =
    L.filter (expr_to_xor_list expression) ~f:is_random_oracle_expr
    |> L.filter ~f:(function | Rand(_,list) -> not (L.exists list ~f:(fun e -> not (can_be_generated e known_terms)))
                             | _ -> assert false
                   )
  in
  let all_known_terms = known_terms @ random_oracle_terms |> L.dedup ~compare:compare_expr in
  let matrix, vector =
    L.map xor_atoms
      ~f:(fun a ->
        let row = L.map all_known_terms ~f:(fun t -> if L.mem ~equal:equal_expr (expr_to_xor_list t) a then 1 else 0) in
        row, (if L.mem ~equal:equal_expr (expr_to_xor_list expression) a && not (is_zero_expr expression) then Leaf "1" else Zero)
      )
    |> L.unzip
  in
  match has_solution matrix vector with
  | None -> false
  | Some _ -> true
                
let rec is_zero_row row =
  match row with
  | [] -> true
  | a :: rest -> if a = 0 then is_zero_row rest else false
              
let solve_system matrix vector =
  let reduced, col_pivots, vector = xor_gaussian_elimination matrix vector in
  if (L.exists (L.zip_exn reduced vector)
         ~f:(fun (row,b) -> if (is_zero_row row) && (not (is_zero_expr b)) then true else false)) then
    None
  else
    Some (L.map (range 0 (L.length (L.hd_exn reduced)))
              ~f:(fun i -> if not (L.mem col_pivots i) then VAR i
                           else
                             let row, v_el = L.find_exn (L.zip_exn reduced vector) ~f:(fun (row,_) -> (L.nth_exn row i) <> 0) in
                             let free_in_this_row =
                               L.filter (range 0 (L.length row))
                                        ~f:(fun j -> let el = L.nth_exn row j in (el <> 0) && not(L.mem col_pivots j)) 
                             in
                             let var_terms = L.fold_left free_in_this_row ~init:Zero ~f:(fun vars v -> XOR(vars, VAR v)) in
                             full_simplify (XOR(v_el, var_terms))
                 )
         )
         
let simulator_knowledge commands =
  let rec aux expressions known_terms knowledge = function
    | [] -> knowledge
    | cmd :: rest_cmds ->
       begin match cmd with
       | Sample_cmd name -> aux (Map.add expressions ~key:name ~data:(Leaf name)) known_terms knowledge rest_cmds
       | F_cmd (name, (var, id)) ->
          let new_k = Map.find_exn expressions var in
          let new_known_terms = known_terms @ [new_k] @ [F(new_k, id)] |> L.dedup ~compare:compare_expr in
          let new_term = F(new_k, id) in
          let new_knowledge =
            begin match L.find knowledge ~f:(fun (expr,_) -> equal_expr expr new_k) with
            | Some _ -> knowledge
            | None   ->
               if can_be_generated new_k known_terms then knowledge @ [(new_term, new_known_terms)]
               else knowledge @ [(new_term, [])]
            end
          in
          aux (Map.add expressions ~key:name ~data:new_term ) new_known_terms new_knowledge rest_cmds
       | R_cmd (names, _, vars) ->
          let new_variables =
            let vars = L.map vars ~f:(fun v -> Map.find_exn expressions v) in
            L.map (range 0 (L.length names)) ~f:(fun i -> Rand (i, vars))
          in
          let expressions' =
            L.fold_left (L.zip_exn names new_variables)
                   ~init:expressions
                   ~f:(fun emap (name,var) -> Map.add emap ~key:name ~data:var )
          in
          aux expressions' known_terms knowledge rest_cmds

       | XOR_cmd (name, vars) ->
          let new_variables = L.map vars ~f:(fun v -> Map.find_exn expressions v) in
          let new_expression =
            L.fold_left (L.tl_exn new_variables)
                   ~init:(L.hd_exn new_variables)
                   ~f:(fun expr v -> XOR(expr, v))
          in
          aux (Map.add expressions ~key:name ~data:(simplify_expr new_expression) ) known_terms knowledge rest_cmds

       | Check (_) -> aux expressions known_terms knowledge rest_cmds
       end
  in
  assert_commands commands;
  aux String.Map.empty [] [] commands

let get_all ~filter system =
  let rec aux variables = function
    | [] -> variables
    | eq :: rest ->
       let new_vars = L.fold_left eq ~init:variables ~f:(fun vars term ->
                                    if filter term && not (L.mem vars term) then vars @ [term] else vars) in
       aux new_vars rest
  in
  aux [] system

let build_system expressions id_map =
  let variables = get_all ~filter:(function | Var _ -> true | _ -> false) expressions in
  L.map expressions ~f:(fun e ->
          L.map variables ~f:(fun v -> if L.mem e v then 1 else 0),
          L.fold_left e ~init:Zero ~f:(fun expr t ->
                        match t with
                        | Const(i,_) ->
                           let this_expr, _ = Map.find_exn id_map i in
                           XOR(expr, this_expr)
                        | _ -> expr
                      )
          |> full_simplify
        )
  |> L.unzip
              
let simulated_world_equations commands =
  let _, equations   = inline_adversary ~real:true commands in
  let expressions, _ = inline_adversary ~real:false commands in
  let equalities, inequalities =
    L.fold_left equations
            ~init:([],[])
            ~f:(fun (l1,l2) (b,var1,eq,var2) ->
              let expr = full_simplify (XOR(Map.find_exn expressions var1, Map.find_exn expressions var2)) in
              match b, eq with
              | true, Eq | false, Ineq -> (l1 @ [expr]), l2
              | _ -> l1, (l2 @ [expr])
            )
  in
  let id_map, _, all_exprs = expressions_to_simulator_terms (equalities @ inequalities) in
  let exprs = L.slice all_exprs 0 (L.length equalities) in  (* Remove inequalities *)
  
  L.iter (Map.to_alist id_map) ~f:(fun (i,(e,_)) -> F.printf "a%d -> %a\n" i pp_expr e);
  L.iter exprs ~f:(fun e -> F.printf "\nt[%a]\n" (pp_list ", " pp_simulator_term) e);
  
  let matrix, vector = build_system exprs id_map in
  let solution = solve_system matrix vector in
  let () = match solution with
    | None -> F.printf "No solution\n"
    | Some s ->
       let all_vars = get_all ~filter:(function | Var _ -> true | _ -> false) all_exprs in
       let max_i = L.fold_left (get_all ~filter:is_var_expr [s])
                               ~init:0
                               ~f:(fun max v -> begin match v with | VAR j -> if j > max then j else max | _ -> assert false end)
       in
       let extra_vars = L.map (range 0 ((L.length all_vars) - (L.length s))) ~f:(fun j -> VAR (j+max_i)) in
       L.iter (L.zip_exn all_vars (s @ extra_vars))
              ~f:(function
                  | Var (j,_), e ->
                     let v, _ = Map.find_exn id_map j in
                     F.printf "bbb %a = %a\n" pp_expr v pp_expr e
                  | _ -> assert false
                 )
  in
  match solution with
  | None -> failwith "No solution"
  | Some s ->
     let all_vars = get_all ~filter:(function | Var _ -> true | _ -> false) all_exprs in
     let max_i = L.fold_left (get_all ~filter:is_var_expr [s])
                      ~init:0
                      ~f:(fun max v -> begin match v with | VAR j -> if j > max then j else max | _ -> assert false end)
     in
     let extra_vars = L.map (range 0 ((L.length all_vars) - (L.length s))) ~f:(fun j -> VAR (j+max_i)) in
     let max_i = max_i + ((L.length all_vars) - (L.length s)) in

     let replace_vars list =
       L.fold_left (L.zip_exn all_vars (s @ extra_vars))
         ~init:list
         ~f:(fun updated (v,e) ->
           begin match v with
           | Var (j,_) ->
              let old, _ = Map.find_exn id_map j in
              L.map updated ~f:(substitute_expr ~old ~by:e )
           | _ -> updated
           end
         )
       |> L.map ~f:full_simplify
     in
     let new_inequalities = replace_vars inequalities in
     let sol = s in
     let s = replace_vars s in

     let knowledge = simulator_knowledge commands in
     
     F.printf "eoooo [%a]\n" (pp_list ", " pp_expr) s;
     F.printf "eoooo [%a]\n" (pp_list ", " pp_expr) sol;
     F.printf "eoooo [%a]\n" (pp_list ", " pp_expr) extra_vars;
     let all_terms_in_precedences, precedences, max_idx = 
       L.fold_left (L.rev (L.zip_exn all_vars (s @ extra_vars)))
         ~init:([],[],max_i)
         ~f:(fun (accum_knowledge, equations, var_index) (v,e) ->
           begin match v with
           | Var (j,_) ->
              let this_var, _ = Map.find_exn id_map j in
              begin match (L.find knowledge ~f:(fun (expr, _) -> equal_expr expr this_var)) with
              | Some (_, this_knowledge) ->
                   let random_oracle_terms =
                     L.filter (expr_to_xor_list e) ~f:is_random_oracle_expr
                     |> L.filter ~f:(function | Rand(_,list) -> not (L.exists list ~f:(fun e' -> not (can_be_generated e' this_knowledge)))
                                              | _ -> assert false
                                    )
                   in
                   let this_knowledge = (L.map this_knowledge ~f:expr_to_xor_list |> L.concat |> L.dedup ~compare:compare_expr) @
                                          random_oracle_terms @ [VAR var_index] in
                   (accum_knowledge @ this_knowledge @ (L.filter (expr_to_xor_list e) ~f:(fun a-> not(is_var_expr a)))
                    |> L.dedup ~compare:compare_expr,
                    equations @ [(this_knowledge, e)],
                    var_index + 1
                   )
              | None -> assert false
              end
           | _ -> assert false
           end
         )
     in

     let precedences = L.map precedences ~f:(fun (l,e) -> (replace_vars l, L.hd_exn (replace_vars [e]))) in
     
     (* Build the system *)
     let variables =
       L.fold_left precedences
          ~init:[]
          ~f:(fun list (_,e) -> list @ (L.filter (expr_to_xor_list e) ~f:(function | VAR _ -> true | _ -> false)) |> L.dedup)
     in

     (* Add terms from inequalities to all_terms_in_precedences *)
     let all_terms_in_precedences = (all_terms_in_precedences @
                                       (L.map inequalities ~f:(fun ineq -> (expr_to_xor_list ineq)) |> L.concat))
                                    |> replace_vars
                                    |> L.map ~f:(fun e -> expr_to_xor_list e ) |> L.concat
                                    |> L.dedup ~compare:compare_expr
                                    |> L.filter ~f:(fun a -> not (L.mem variables a ~equal:equal_expr ))
     in
     
     let vars_matrix, matrix, vector =
       L.fold_left precedences
          ~init:([],[],[])
          ~f:(fun (vars_matrix, matrix, vector) (k,e) ->
            let vars_matrix', matrix', vector' =
              L.map all_terms_in_precedences
                ~f:(fun t ->
                  L.map variables ~f:(fun v ->
                          L.map all_terms_in_precedences ~f:(fun tt ->
                                  if L.mem (expr_to_xor_list t) tt && L.mem (expr_to_xor_list e) v then 1
                                  else 0)
                        )
                  |> L.concat,
                  L.map k ~f:(fun tt -> if L.mem (expr_to_xor_list tt) t then 1 else 0),
                  if L.mem (expr_to_xor_list e) t then Leaf "1" else Zero
                ) |> unzip3
            in
            if L.length matrix' = 0 then vars_matrix, matrix, vector
            else
              let matrix'' =
                (L.map matrix ~f:(fun row -> row @ (list_repeat 0 (L.length (L.hd_exn matrix')))) ) @
                  (if L.length matrix = 0 then matrix'
                   else L.map matrix' ~f:(fun row -> (list_repeat 0 (L.length (L.hd_exn matrix))) @ row)
                  )
              in
              (vars_matrix @ vars_matrix'), matrix'', (vector @ vector')
          )
     in

     let matrix = L.zip_exn vars_matrix matrix |> L.map ~f:(fun (row,row') -> row @ row') in
     
     F.printf "\n Inequalities:\n";
     L.iter inequalities ~f:(fun e -> F.printf "%a <> 0\n" pp_expr e);
     F.printf "End\n";
     F.printf "\n Inequalities:\n";
     L.iter new_inequalities ~f:(fun e -> F.printf "%a <> 0\n" pp_expr e);
     F.printf "End\n";

     F.printf "\n Precedences:\n";     
     L.iter precedences ~f:(fun (k,e) -> F.printf "%a -> [%a]\n" pp_expr e (pp_list ", " pp_expr) k);
     F.printf "\n\n[%a]\n" (pp_list ", " pp_expr) all_terms_in_precedences;
     F.printf "End\n\n\n\n";

     let solution = solve_system matrix vector in
     begin match solution with
     | None -> F.printf "No solution\n"
     | Some s ->
        let s = L.map s ~f:(function | VAR j -> VAR (j+max_idx) | a -> a) in
        F.printf "[%a]\n" (pp_list "\n" pp_expr) s;
        let free_vars_lincomb =
          L.map (range 0 (L.length variables))
                ~f:(fun i ->
                  let n = L.length all_terms_in_precedences in
                  let lincomb = L.zip_exn (L.slice s (i*n) ((i+1)*n)) all_terms_in_precedences in
                  (L.nth_exn variables i, lincomb)
                )
        in
        let conjunction =
          L.map new_inequalities
            ~f:(fun ineq ->
              let terms_in_ineq = expr_to_xor_list ineq in
              L.map all_terms_in_precedences
                 ~f:(fun term ->
                   let coeff = if L.mem terms_in_ineq term ~equal:equal_expr then Leaf "1" else Zero in
                   L.fold_left free_vars_lincomb
                      ~init:coeff
                      ~f:(fun c (v, list) ->
                        if L.mem terms_in_ineq v ~equal:equal_expr then
                          let (c',_) = L.find_exn list ~f:(fun (_,e) -> equal_expr e term) in
                          full_simplify (XOR(c,c'))
                        else c
                      )                     
                 )
              |> L.filter ~f:(fun e -> not (is_zero_expr e))
            )
        in
        L.iter conjunction ~f:(fun list -> L.iter list ~f:(fun e -> F.printf " %a = 1 \\/" pp_expr e ); F.printf "\n/\\\n");
        
        let make_disj_poly e =
          L.fold_left (expr_to_xor_list e)
             ~init:Z2P.zero
             ~f:(fun p t ->
               match t with
               | VAR i -> Z2P.((of_var i) +! p)
               | Leaf s when s = "1" -> Z2P.(one +! p)
               | Zero -> p
               | _ -> assert false
             )
        in        
        let f list =
          let p = L.fold_left list ~init:Z2P.one ~f:(fun p e -> Z2P.(p *! (make_disj_poly e))) in
          match find_zero Z2P.(p +! one) with
          | None -> false
          | Some _ -> true
        in       

        let solved = lazy_find ~f conjunction in
        begin match solved with
        | None -> F.printf "Nope\n"
        | Some s ->
           F.printf "Yeah!\n";
           let p = L.fold_left s ~init:Z2P.one ~f:(fun p e -> Z2P.(p *! (make_disj_poly e))) in
           match find_zero Z2P.(p +! one) with
           | None -> assert false
           | Some integers ->
              F.printf "[%a]\n\n" (pp_list ", " pp_int) integers;
              let free_vars =
                L.map free_vars_lincomb ~f:(fun (v,lincomb) ->
                        let comb = L.fold_left lincomb
                                       ~init:Zero
                                       ~f:(fun comb (var,e) ->
                                         begin match var with
                                         | VAR i when L.mem integers i -> full_simplify (XOR(comb, e))
                                         | _ -> comb
                                         end                          
                                       )
                        in
                        F.printf "%a -> %a\n" pp_expr v pp_expr comb;
                        (v, comb)
                      )
              in
              F.printf "\n\n";
              let simulator_terms =
                L.map (L.rev (L.zip_exn all_vars (sol @ extra_vars)))
                      ~f:(function
                          | Var (j,_), e ->
                             let v, _ = Map.find_exn id_map j in
                             let e' = L.fold_left (expr_to_xor_list e)
                                                  ~init:Zero
                                                  ~f:(fun e' t ->
                                                    begin match L.find free_vars ~f:(fun (v,_) -> equal_expr v t) with
                                                    | None -> XOR(e',t)
                                                    | Some (_,comb) -> XOR(e',comb)
                                                    end
                                                  )
                                      |> full_simplify
                             in
                             F.printf "%a = %a = %a\n" pp_expr v pp_expr e pp_expr e';
                             (v,e,e')
                          | _ -> assert false
                         )
              in
              F.printf "\n\n";
              ()
        end
     end
       
