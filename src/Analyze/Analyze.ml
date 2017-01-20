open Core_kernel.Std
open Abbrevs
open Expressions
open Simulator

let input_file filename =
  let in_channel = open_in filename in
  let rec go lines =
    try
      let l = input_line in_channel in
      go (l :: lines)
    with
      End_of_file -> lines
  in
  let lines = go [] in
  let _ = close_in_noerr in_channel in
  String.concat ~sep:"\n" (L.rev lines)

let print_time t1 t2 =
  F.printf "\nTime: %F seconds\n" (Pervasives.ceil ((10000.0 *. (t2 -. t1))) /. 10000.0)
  
                
let analyze_commands cmds =
  let t1 = Unix.gettimeofday() in
  let commands = Parse.p_cmds cmds |> Eval.eval_cmds in
  let simulated = simulated_world_equations commands in
  let t2 = Unix.gettimeofday() in
  (match simulated with
  | None -> F.printf "The attacker is universal\n";
            print_time t1 t2;
  | Some l ->
     F.printf "There exists a simulator for the attacker:\n\n";
     L.iter l ~f:(fun (v,e) -> F.printf "%a = %a\n" pp_expr v pp_expr e);
     print_time t1 t2;
  );
  exit 0
