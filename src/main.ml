(* Main function of the tool *)

open Core_kernel.Std
open Abbrevs

let main =
  if Array.length Sys.argv <> 2 then
    output_string stderr (F.sprintf "usage: %s <scheme file>\n" Sys.argv.(0))
  else
    Analyze.analyze_commands (Analyze.input_file Sys.argv.(1))
