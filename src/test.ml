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
 (*     R_cmd(["u";"v"], feistel_cipher, ["x0";"x1"]); (* Remove later this line *)
      F_cmd("j", ("u",3)); (* Remove later this line *) *)
      F_cmd("v3", ("x3", 3));
      XOR_cmd("x4", ["x2";"v3"]);
      R_cmd(["v5";"v4"], feistel_cipher, ["x0";"x1"]);
      Check("v1", Eq, "v2");
      Check("v4", Eq, "x4");
(*      Check("v4", Eq, "x3");*)
    ]
  in
  let _ = simulated_world_equations commands in
  let knowledge = simulator_knowledge commands in
  L.iter knowledge ~f:(fun (expr, list) -> F.printf "Knowledge %a -> [%a]\n" pp_expr expr (pp_list ", " pp_expr) list);


  (*let matrix = [[1;1;1;1];[0;1;1;0];[1;1;1;0]] in
  let vector = [Leaf "a"; Leaf "b"; Leaf "c"] in
  F.printf "%a\n" (pp_matrix pp_int) matrix;
  F.printf "[%a]\n" (pp_list "," pp_expr) vector;

  let reduced, col_pivots, vector' = xor_gaussian_elimination matrix vector in
  F.printf "%a\n" (pp_matrix pp_int) reduced;
  F.printf "[%a]\n" (pp_list "," pp_int) col_pivots;
  F.printf "[%a]\n\n\n" (pp_list "," pp_expr) vector';


  let solution = solve_system matrix vector in
  let () = match solution with
    | None -> F.printf "No solution\n"
    | Some s ->
       L.iter s ~f:(function
                    | Value (e, indices) -> F.printf "%a + [%a]\n" pp_expr e (pp_list " + " pp_int) indices
                    | Free i -> F.printf "Free %d\n" i
                   )
  in
   *)

  F.printf "Test\n\n";
  let x1 = Leaf "x1" in
  let x2 = Leaf "x2" in
  let known = [x1; x2] in
  let expr = Rand(2, [Rand(1,[x1;x2]); Rand(1,[x1;x1])]) in
  F.printf "%a -> %b\n\n" pp_expr expr (can_be_generated expr known);  
  ()
