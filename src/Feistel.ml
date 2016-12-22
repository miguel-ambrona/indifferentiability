(* Feistel network functions *)

open Core_kernel.Std
open Expressions

(* ** Feistel functions *)

let feistel_round left right i =
  right, XOR(left, F(right, i))

let feistel_enc left right rounds =
  let rec aux l r k =
    if k = rounds then r, l
    else
      let l, r = feistel_round l r k in
      aux l r (k+1)
  in
  aux left right 0

let feistel_dec right left rounds =
  let rec aux r l k =
    if k < 0 then l, r
    else
      let r, l = feistel_round r l k in
      aux r l (k-1)
  in
  aux right left (rounds-1)
