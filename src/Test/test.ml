(* Test *)

open Abbrevs
open Expressions
open Feistel
open Attacker
open Simulator

let test_feistel_attack () =

  (* Attack on 5-rounds Feistel *)

  let x3 = Leaf "x3" in
  let x3' = Leaf "x3'" in
  let x4 = Leaf "x4" in
  let x2 = XOR(x4, F(x3, 3)) in
  let x2' = XOR(x4, F(x3', 3)) in
  let x1 = XOR(x3, F(x2, 2)) in
  let x1' = XOR(x3', F(x2', 2)) in
  let x1'' = XOR(x3', F(x2, 2)) in
  let x1''' = XOR(x3, F(x2', 2)) in
  let x0 = XOR(x2, F(x1, 1)) in
  let x0' = XOR(x2', F(x1', 1)) in
  let x0'' = XOR(x2, F(x1'', 1)) in
  let x0''' = XOR(x2', F(x1''', 1)) in

  let _, x5 = feistel_enc x0 x1 5 in
  let _, x5' = feistel_enc x0' x1' 5 in
  let _, x5'' = feistel_enc x0'' x1'' 5 in
  let _, x5''' = feistel_enc x0''' x1''' 5 in

  let xor_x1 = full_simplify (XOR(x1, XOR(x1', XOR(x1'', x1''')))) in
  let xor_x5 = full_simplify (XOR(x5, XOR(x5', XOR(x5'', x5''')))) in
  F.printf "x1 + x1' + x1'' + x1''' = %a\n" pp_expr xor_x1;
  F.printf "x5 + x5' + x5'' + x5''' = %a\n\n" pp_expr xor_x5;
  ()

let testa = test_feistel_attack
    
let test () =
  let feistel_cipher =
    { n_in = 2; n_out = 2;
      cipher = (fun inputs -> let l, r = feistel_enc (L.nth_exn inputs 0) (L.nth_exn inputs 1) 2 in [l; r]);
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
      Check("v4", Eq, "0");
      Check("v3", Eq, "0");
      Check("v2", Eq, "0");
    ]
  in
  (* 
  let commands =
    [
      Sample_cmd ("x3");
      Sample_cmd ("x3'");
      Sample_cmd ("x4");
      
      F_cmd("f1", ("x3", 3));
      F_cmd("f2", ("x3'", 3));
      XOR_cmd("x2", ["x4"; "f1"]);
      XOR_cmd("x2'", ["x4"; "f2"]);

      F_cmd("f3", ("x2", 2));
      F_cmd("f4", ("x2'", 2));
      XOR_cmd("x1", ["x3"; "f3"]);
      XOR_cmd("x1'", ["x3'"; "f4"]);
      XOR_cmd("x1''", ["x3'"; "f3"]);
      XOR_cmd("x1'''", ["x3"; "f4"]);

      F_cmd("f5", ("x1", 1));
      F_cmd("f6", ("x1'", 1));
      F_cmd("f7", ("x1''", 1));
      F_cmd("f8", ("x1'''", 1));
      XOR_cmd("x0", ["x2"; "f5"]);
      XOR_cmd("x0'", ["x2'"; "f6"]);
      XOR_cmd("x0''", ["x2"; "f7"]);
      XOR_cmd("x0'''", ["x2'"; "f8"]);      
      
      
      R_cmd(["x6";"x5"], feistel_cipher, ["x0";"x1"]);
      R_cmd(["x6'";"x5'"], feistel_cipher, ["x0'";"x1'"]);
      R_cmd(["x6''";"x5''"], feistel_cipher, ["x0''";"x1''"]);
      R_cmd(["x6'''";"x5'''"], feistel_cipher, ["x0'''";"x1'''"]);

      XOR_cmd("v1", ["x1"; "x1'"; "x1''"; "x1'''"]);
      XOR_cmd("v2", ["x5"; "x5'"; "x5''"; "x5'''"]);
      
      Check("v1", Eq, "0");
      Check("v2", Eq, "0");
    ]
  in
   *)
  let simulated = simulated_world_equations commands in
  match simulated with
  | None -> F.printf "The attacker is universal\n"
  | Some l ->
     L.iter l ~f:(fun (v,e) -> F.printf "%a = %a\n" pp_expr v pp_expr e);
     F.printf "There exists a simulator for that attacker\n"
                 
