(* Util functions *)

open Abbrevs

let range i j =
  let rec aux output k =
    if k >= j then output
    else aux (output @ [k]) (k+1)
  in
  aux [] i

let pp_int _ i = F.printf "%d" i
      
let string_of_list sep string_of_a list =
  let rec aux output = function
    | []        -> output
    | a :: []   -> output ^ (string_of_a a)
    | a :: rest -> aux (output ^ (string_of_a a) ^ sep) rest
  in
  aux "" list
       
let rec pp_list sep pp_elt f l =
  match l with
  | [] -> ()
  | [e] -> pp_elt f e
  | e::l -> F.fprintf f "%a%(%)%a" pp_elt e sep (pp_list sep pp_elt) l

let rec compare_lists ~compare list1 list2 =
  let list1 = L.sort ~cmp:compare list1 in
  let list2 = L.sort ~cmp:compare list2 in
  match list1, list2 with
  | [], [] -> 0
  | [], _  -> -1
  | _ , [] -> +1
  | a :: rest1, b :: rest2 ->
     let c = compare a b in
     if c = 0 then compare_lists ~compare rest1 rest2 else c
