(* Defining the simulator *)

open Core_kernel.Std
open Abbrevs
open Expressions
open Attacker

(* ** Simulator functions *)

type simulator_term =
  | Const of int * (int list)      (* constant id  *  constant dependent terms *)
  | Var   of int * (int list)      (* variable id  *  variable dependent terms *)
(*
let expressions_to_simulator_terms expressions =
  let rec aux id_map id_counter converted = function
    | [] -> id_map, id_counter, converted
    | e :: rest ->
       let xor_list = expr_to_xor_list e in
       let new_expr =
         L.fold_left xor_list
             ~init:(id_map, id_counter, [])
             ~f:(fun non_xor_term (id_map, id_counter, terms) ->
               begin match non_xor_term with
               | F(expr, i) ->
                  let id_map, id_counter, _ = aux id_map id_counter [] [expr] in
                  Var(id_counter, L.map (expr_to_xor_list expr) ~f:(fun e' -> Map.find_exn )

             )
 *)                    
let simulated_world_equations commands =
  let _, equations   = inline_adversary ~real:true commands in
  let expressions, _ = inline_adversary ~real:false commands in
  let equalities, inequalities =
    L.fold_left equations
            ~init:([],[])
            ~f:(fun (l1,l2) (b,var1,eq,var2) ->
              let expr = XOR(Map.find_exn expressions var1, Map.find_exn expressions var2) in
              match b, eq with
              | true, Eq | false, Ineq -> (l1 @ [expr]), l2
              | _ -> l1, (l2 @ [expr])
            )
  in
  ()


