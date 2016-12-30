(* Defining the simulator *)

open Core_kernel.Std
open Abbrevs
open Util
open Expressions
open Attacker

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
               | Leaf(_) ->
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
               | Zero -> fixme "This should not be executed"
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
  let rec go reduced vector col non_used_rows =
    if col >= n then reduced, vector
    else
      (* We search for a non-zero in column col and a non-used row *)
      match search_for_non_zero non_used_rows col reduced with
      | None -> go reduced vector (col+1) non_used_rows
      | Some row ->
         let reduced, vector = reduce_by_pivot row col reduced vector in
         go reduced vector (col+1) (L.filter non_used_rows ~f:(fun r -> r <> row))
  in
  go matrix vector 0 (range 0 m)

let has_solution matrix vector =
  let reduced, vector = xor_gaussian_elimination matrix vector in
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

let can_be_generated expression known_terms =
  let expression = simplify_expr expression in
  let known_terms = L.map known_terms ~f:simplify_expr in
  let xor_atoms =
    (expr_to_xor_list expression) @ (L.concat (L.map known_terms ~f:expr_to_xor_list ))
    |> L.dedup ~compare:compare_expr
  in
  let matrix, vector =
    L.map xor_atoms
      ~f:(fun a ->
        let row = L.map known_terms ~f:(fun t -> if L.mem ~equal:equal_expr (expr_to_xor_list t) a then 1 else 0) in
        row, (if L.mem ~equal:equal_expr (expr_to_xor_list expression) a then Leaf "1" else Zero)
      )
    |> L.unzip
  in
  match has_solution matrix vector with
  | None -> false
  | Some _ -> true

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

let simulated_world_equations commands =
  let _, equations   = inline_adversary ~real:true commands in
  let expressions, _ = inline_adversary ~real:false commands in
  let equalities, _inequalities =
    L.fold_left equations
            ~init:([],[])
            ~f:(fun (l1,l2) (b,var1,eq,var2) ->
              let expr = XOR(Map.find_exn expressions var1, Map.find_exn expressions var2) in
              match b, eq with
              | true, Eq | false, Ineq -> (l1 @ [expr]), l2
              | _ -> l1, (l2 @ [expr])
            )
  in
  let id_map, _, exprs = expressions_to_simulator_terms equalities in
  L.iter (Map.to_alist id_map) ~f:(fun (i,(e,_)) -> F.printf "%d -> %a\n" i pp_expr e);
  F.printf "\n[%a]\n" (pp_list ", " pp_simulator_term) (L.hd_exn exprs);
  ()
