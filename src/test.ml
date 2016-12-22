(* Test *)

open Abbrevs
open Expressions
open Feistel

let test () =

  (* Attack on 5-rounds Feistel *)

  let x3 = Leaf "x3" in
  let x3' = Leaf "x3'" in
  let x4 = Leaf "x4" in
  let x2 = XOR(x4, F(x3, 2)) in
  let x2' = XOR(x4, F(x3', 2)) in
  let x1 = XOR(x3, F(x2, 1)) in
  let x1' = XOR(x3', F(x2', 1)) in
  let x1'' = XOR(x3', F(x2, 1)) in
  let x1''' = XOR(x3, F(x2', 1)) in
  let x0 = XOR(x2, F(x1, 0)) in
  let x0' = XOR(x2', F(x1', 0)) in
  let x0'' = XOR(x2, F(x1'', 0)) in
  let x0''' = XOR(x2', F(x1''', 0)) in

  let _, x5 = feistel_enc x0 x1 5 in
  let _, x5' = feistel_enc x0' x1' 5 in
  let _, x5'' = feistel_enc x0'' x1'' 5 in
  let _, x5''' = feistel_enc x0''' x1''' 5 in
  let xor_x1 = simplify_expr (XOR(x1, XOR(x1', XOR(x1'', x1''')))) in
  let xor_x5 = simplify_expr (XOR(x5, XOR(x5', XOR(x5'', x5''')))) in
  F.printf "x1 + x1' + x1'' + x1''' = %a\n" pp_expr xor_x1;
  F.printf "x5 + x5' + x5'' + x5''' = %a\n\n" pp_expr xor_x5;
