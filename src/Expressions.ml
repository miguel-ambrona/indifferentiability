(* Expressions and simplification functions *)

open Core_kernel.Std
open Abbrevs

(* ** Expressions *)

type expression =
  | F    of expression * int
  | XOR  of expression * expression
  | Leaf of string
  | Zero


(* ** Pretty printing *)

let rec string_of_expr = function
  | F(expr, i)  -> "F" ^ (string_of_int (i+1)) ^ "(" ^ (string_of_expr expr) ^ ")"
  | XOR(e1, e2) -> (string_of_expr e1) ^ " + " ^  (string_of_expr e2)
  | Leaf(s)     -> s
  | Zero        -> "0"

let pp_expr _fmt expr =
  F.printf "%s" (string_of_expr expr)


(* ** Simplification functions *)

let rec compare_expr e1 e2 =
  match e1, e2 with
  | F(e1',i1), F(e2',i2) ->
     let c = Int.compare i1 i2 in
     if c = 0 then compare_expr e1' e2'
     else c
  | F(_,_), _ -> -1
  | _, F(_,_) -> +1
  | XOR(e1',e1''), XOR(e2',e2'') ->
     let c = compare_expr e1' e2' in
     if c = 0 then compare_expr e1'' e2''
     else c
  | XOR(_,_), _ -> -1
  | _, XOR(_,_) -> +1
  | Leaf(s1), Leaf(s2) -> S.compare s1 s2
  | Leaf(_), _ -> -1
  | _, Leaf(_) -> +1
  | Zero, Zero -> 0

let equal_expr e1 e2 = compare_expr e1 e2 = 0

let rec expr_to_xor_list = function
  | XOR (e1, e2) -> (expr_to_xor_list e1) @ (expr_to_xor_list e2)
  | e -> [e]

let xor_list_to_expr list =
  let rec aux expr = function
    | [] -> expr
    | a :: rest -> aux (XOR(expr, a)) rest
  in
  match list with
  | [] -> Zero
  | a :: rest -> aux a rest

let rec simplify_expr expr =
  let xor_list = expr_to_xor_list expr in
  match xor_list with
  | [] -> Zero
  | a :: [] ->
     begin match a with
     | F(e1,i) -> F(simplify_expr e1, i)
     | _ -> a
     end
  | _ ->
     let xor_list = L.sort ~cmp:compare_expr (L.map xor_list ~f:simplify_expr) in
     let rec aux simplified_list current k = function
       | [] ->
          if k%2 = 0 then simplified_list
          else simplified_list @ [current]
       | a :: rest ->
          if equal_expr current a then aux simplified_list current (k+1) rest
          else
            if k%2 = 0 then aux simplified_list a 1 rest
            else aux (simplified_list @ [current]) a 1 rest
     in
     xor_list_to_expr (aux [] Zero 0 xor_list)

let full_simplify expr =
  let rec aux last expr =
    if equal_expr last expr then expr
    else aux expr (simplify_expr expr)
  in
  aux expr (simplify_expr expr)
