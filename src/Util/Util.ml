(* Util functions *)

open Abbrevs

let range i j =
  let rec aux output k =
    if k >= j then output
    else aux (output @ [k]) (k+1)
  in
  aux [] i

let list_repeat a n =
  let rec aux output k =
    if k >= n then output
    else aux (a :: output) (k+1)
  in
  aux [] 0

let pp_int _ i = F.printf "%d" i
let pp_string _ s = F.printf "%s" s

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

let pp_matrix pp_elt f m =
  L.iter m ~f:(F.fprintf f "[%a]\n" (pp_list ", " pp_elt))

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
                                                             
let unzip3 list =
  let rec aux l1 l2 l3 = function
    | [] -> l1,l2,l3
    | (a,b,c) :: rest -> aux (l1 @ [a]) (l2 @ [b]) (l3 @ [c]) rest
  in
  aux [] [] [] list

let find_position list ~f =
  let rec aux k = function
    | [] -> failwith "Not found"
    | a :: rest -> if f a then k else aux (k+1) rest
  in
  aux 0 list
      
let rec lazy_find ~f l =
  (* This function takes l, which is a list of lists of the shape:
     [[a1,b1,...z1], ..., [an,bn,...wn]] and for every combination of elements:
     (_1, _2, ..., _n) evaluates f. If f holds it immediatly returns the tuple,
     if f never holds, it will return false *)
  let rec aux = function
    | [] -> None
    | a :: [] ->
       begin match a with
       | [] -> None
       | el :: rest -> if f [el] then Some [el] else aux [rest]
       end
    | a :: rest_lists ->
       begin match a with
       | [] -> None
       | el :: rest ->
          begin match lazy_find ~f:(fun l -> f (el :: l)) rest_lists with
          | None -> aux (rest :: rest_lists)
          | Some s -> Some (el :: s)
          end
       end
  in
  aux l

let all_element_and_rest l =
  let n = L.length l in
  let rec aux k output = function
    | [] -> []
    | a :: rest ->
       if k = n then output
       else aux (k+1) ((a,rest) :: output) (rest @ [a])
  in
  aux 0 [] l
      
let rec split_in_all_pairs = function
  | [] -> []
  | _ :: [] -> failwith "the list has an odd number of elements"
  | a :: b :: [] -> [[(a,b)]]
  | a :: rest ->
     let all_second = all_element_and_rest rest in
     L.map all_second ~f:(fun (b,restb) -> L.map (split_in_all_pairs restb) ~f:(fun pairs_l -> (a,b) :: pairs_l) )
     |> L.concat

let exists_duplicate ~equal list =
  let rec aux = function
    | [] -> false
    | a :: rest ->
       if L.mem rest a ~equal then true
       else aux rest
  in
  aux list
