(* Expressions and simplification functions *)

open Core_kernel.Std
open Abbrevs
open Util

(* ** Expressions *)

type expression =
  | F    of expression * int * (string option)
  | XOR  of expression * expression
  | Leaf of string
  | Zero
  | Rand of int * (expression list) * (string option)
  | VAR  of int (* Variable, non-determined expression *)


(* ** Pretty printing *)

let rec string_of_expr = function
  | F(expr, i, fname)  ->
     begin match fname with
     | None -> "F" ^ (string_of_int i) ^ "(" ^ (string_of_expr expr) ^ ")"
     | Some name -> name ^ (string_of_int i) ^ "(" ^ (string_of_expr expr) ^ ")"
     end
  | XOR(e1, e2) -> (string_of_expr e1) ^ " + " ^  (string_of_expr e2)
  | Leaf(s)     -> s
  | Zero        -> "0"
  | Rand (i, l, oname) ->
     begin match oname with
     | None -> "R" ^ (string_of_int i) ^ "(" ^ (string_of_list "," string_of_expr l) ^ ")"
     | Some name -> name ^ (string_of_int i) ^ "(" ^ (string_of_list "," string_of_expr l) ^ ")"
     end
  | VAR (i)     -> "Var_" ^ (string_of_int i)

let pp_expr _fmt expr =
  F.printf "%s" (string_of_expr expr)


(* ** Simplification functions *)

let rec compare_expr e1 e2 =
  match e1, e2 with
  | Rand (i1,l1,_), Rand (i2,l2,_) ->
     let c = Int.compare i1 i2 in
     if c = 0 then compare_lists ~compare:compare_expr l1 l2
     else c
  | Rand(_,_,_), _ -> -1
  | _, Rand(_,_,_) -> +1
  | F(e1',i1,_), F(e2',i2,_) ->
     let c = Int.compare i1 i2 in
     if c = 0 then compare_expr e1' e2'
     else c
  | F(_,_,_), _ -> -1
  | _, F(_,_,_) -> +1
  | XOR(e1',e1''), XOR(e2',e2'') ->
     let c = compare_expr e1' e2' in
     if c = 0 then compare_expr e1'' e2''
     else c
  | XOR(_,_), _ -> -1
  | _, XOR(_,_) -> +1
  | Leaf(s1), Leaf(s2) -> S.compare s1 s2
  | Leaf(_), _ -> -1
  | _, Leaf(_) -> +1
  | VAR i, VAR j -> Int.compare i j
  | VAR(_), _  -> -1
  | _ , VAR(_) -> +1
  | Zero, Zero -> 0

let equal_expr e1 e2 = compare_expr e1 e2 = 0
                                              
let is_zero_expr = function
  | Zero -> true
  | _ -> false

let is_random_oracle_expr = function
  | Rand _ -> true
  | _ -> false

let is_var_expr = function
  | VAR _ -> true
  | _ -> false
                                              
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
     | F(e1,i,fname)    -> F(simplify_expr e1, i,fname)
     | Rand (i,l,oname) -> Rand(i, L.map l ~f:simplify_expr, oname )
     | _ -> a
     end
  | _ ->
     let xor_list = L.sort ~cmp:compare_expr (L.map xor_list ~f:simplify_expr ) in
     let xor_without_zeros = L.filter xor_list ~f:(fun t -> not (is_zero_expr t)) in
     let xor_list = if L.length xor_without_zeros = 0 then [Zero] else xor_without_zeros in
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

let rec substitute_expr ~old ~by expression =
  if equal_expr old expression then by
  else
    match expression with
    | F(expr, i, fname)  -> F(substitute_expr ~old ~by expr, i, fname)
    | XOR(e1, e2) -> XOR(substitute_expr ~old ~by e1, substitute_expr ~old ~by e2) |> full_simplify
    | Rand (i, l, oname) -> Rand(i, L.map l ~f:(fun e -> substitute_expr ~old ~by e), oname)
    | _ as terminal -> terminal
