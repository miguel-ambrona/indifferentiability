(* Defining the simulator *)

open Core_kernel.Std
open Abbrevs
open Util

type z2_monom = int list

type z2_poly = z2_monom list

let simplify_monom monom =
  L.dedup monom ~compare:Int.compare  (* In Z2, x^2 = x *)
  |> L.sort ~cmp:Int.compare

let compare_monom m1 m2 =
  let rec aux = function
    | ([],[]) -> 0
    | a1 :: rest1, a2 :: rest2 ->
       if Int.compare a1 a2 = 0 then aux (rest1,rest2)
       else Int.compare a1 a2
    | _ -> assert false
  in
  if L.length m1 > L.length m2 then +1
  else if L.length m1 < L.length m2 then -1
  else aux (simplify_monom m1, simplify_monom m2)

let equal_monom m1 m2 = compare_monom m1 m2 = 0

let simplify_poly poly =
  let poly = L.map poly ~f:simplify_monom in
  L.filter poly ~f:(fun a -> (L.count poly ~f:(equal_monom a))%2 = 1)
  |> L.sort ~cmp:compare_monom

let compare_poly p1 p2 =
  let rec aux = function
    | ([],[]) -> 0
    | m1 :: rest1, m2 :: rest2 ->
       if compare_monom m1 m2 = 0 then aux (rest1,rest2)
       else compare_monom m1 m2
    | _ -> assert false
  in
  if L.length p1 > L.length p2 then +1
  else if L.length p1 < L.length p2 then -1
  else aux (simplify_poly p1, simplify_poly p2)

let equal_poly p1 p2 = compare_poly p1 p2 = 0

let sum_poly p1 p2 =
  simplify_poly (p1 @ p2)

let mul_poly p1 p2 =
  L.map p1 ~f:(fun m1 -> L.map p2 ~f:(fun m2 -> m1 @ m2))
  |> L.concat
  |> simplify_poly

module Z2P = struct
  let ( +! ) a b = sum_poly a b
  let ( *! ) a b = mul_poly a b
  let zero = []
  let one = [[]]

  let of_var v = [[v]]
end

let string_of_var v =
  "x" ^ (string_of_int v)

let string_of_monom m =
  if L.length m = 0 then "1"
  else string_of_list "*" string_of_var m

let string_of_poly p =
  if L.length p = 0 then "0"
  else string_of_list " + " string_of_monom p

let pp_z2_poly _fmt p = F.printf "%s" (string_of_poly p)


let find_zero p =
  (* We return a list with non-null variables for the solution *)
  let p = simplify_poly p in
  if L.length p = 0 then Some []
  else if L.length (L.hd_exn p) = 0 then (* There is a constant monomial *)
    if L.length (L.tl_exn p) = 0 then None
    else Some (L.hd_exn (L.tl_exn p))
  else Some []
