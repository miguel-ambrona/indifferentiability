(* Searching for non-trivial equations of Feistel and other ciphers *)

open Core_kernel.Std
open Abbrevs
open Expressions
       
let rec subsets_n_elements l n =
  match n with
  | 0 -> []
  | 1 -> L.map l ~f:(fun a -> [a])
  | _ -> match l with
         | [] -> []
         | (x :: xs) -> (L.map (subsets_n_elements xs (n-1)) ~f:(fun m -> (x::m)))
                        @ (subsets_n_elements xs n)

let subsets_less_than_n l n =
  let rec aux output k =
    if k > n then output
    else aux ((subsets_n_elements l k) @ output) (k+1)
  in
  aux [] 1
                            
let rec zip_all f l1 l2 =
  match l1 with
  | [] -> []
  | x :: xs -> (L.map l2 ~f:(fun y -> f x y)) @ (zip_all f xs l2)
(*
let rec apply_F l maxi =
  let aux l maxi k =
    if k=0 then L.map l ~f:(fun x -> F(x,f, None))

                                                  
let rec generate_shape1 (accum : expression list) (depth : int) (xors : int) (maxi : int) : expression list =
  let rec apply_F e =
      if k = maxi then output
      else aux ((F(e,k,None)) :: output) (k+1)
    in
    aux [] 0
  in
  match xors with
  | 0 ->
     begin match depth with
     | 0 -> accum
     | _ -> generate_shape1 (accum @ (L.concat (L.map accum ~f:apply_F ))) (depth-1) xors maxi
     end
  | _ -> zip_all (fun e1 e2 -> XOR(e1,e2)) accum accum
 *)                                
            
let rec generate_shape (xors : int list) (maxi : int) (atoms : expression list) =
  let apply_F e =
    let rec aux output k =
      if k = maxi then output
      else aux ((F(e,k, None)) :: output) (k+1)
    in
    aux [] 0
  in
  match xors with
  | [] -> atoms
  | this_depth_xor_length :: rest ->
     let previous_depth = generate_shape rest maxi atoms in
     let elements = (L.concat (L.map previous_depth ~f:apply_F )) @ atoms in
     L.map (subsets_less_than_n elements this_depth_xor_length)
           ~f:(fun l -> L.fold_left l
                          ~init:Zero
                          ~f:(fun expr el -> XOR(expr, el))
                        |> full_simplify
              )
