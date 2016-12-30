(* Test *)

open Abbrevs
open Util
open Expressions
open Feistel
open Attacker
open Simulator

let test_feistel_attack () =

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
  ()

let test () =
  let feistel_cipher =
    { n_in = 2; n_out = 2;
      cipher = (fun inputs -> let l, r = feistel_enc (L.nth_exn inputs 0) (L.nth_exn inputs 1) 4 in [l; r]);
    }
  in

  let commands =
    [
      Sample_cmd ("x1");
      Sample_cmd ("x2");
      F_cmd("v1", ("x2", 2));
      F_cmd("v2", ("x1", 1));
      XOR_cmd("x0", ["v2";"x2"]);
      XOR_cmd("x3", ["v1";"x1"]);
      F_cmd("v3", ("x3", 3));
      XOR_cmd("x4", ["x2";"v3"]);
      R_cmd(["v5";"v4"], feistel_cipher, ["x0";"x1"]);
      Check("v1", Eq, "v2");
      Check("v4", Eq, "x4");
    ]
  in
  let _ = simulated_world_equations commands in
  let knowledge = simulator_knowledge commands in
  L.iter knowledge ~f:(fun (expr, list) -> F.printf "%a -> [%a]\n" pp_expr expr (pp_list ", " pp_expr) list);

  let matrix = [[1;1;0;1];[0;1;1;0];[1;1;1;0]] in
  let vector = [Leaf "a"; Leaf "b"; Leaf "c"] in
  F.printf "%a\n" (pp_matrix pp_int) matrix;
  F.printf "[%a]\n" (pp_list "," pp_expr) vector;

  let reduced, vector = xor_gaussian_elimination matrix vector in
  F.printf "%a\n" (pp_matrix pp_int) reduced;
  F.printf "[%a]\n" (pp_list "," pp_expr) vector;
  ()
