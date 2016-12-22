(* Defining attackers *)

open Core_kernel.Std
open Abbrevs
open Expressions
       
(* ** Attack commands *)

type eq = Eq | Ineq
       
type command =
  | Sample_cmd of string
  | F_cmd      of string * (string * int)        (*    output * (input * id)    *)
  | R_cmd      of (string list) * (string list)  (*    outputs * inputs         *)
  | XOR_cmd    of string * (string list)         (*    output * inputs          *)
  | Check      of string * eq * string

let already_exists name = Some ("Variable " ^ name ^ " already exists")
let not_defined var     = Some ("Variable " ^ var ^ " is not defined")
                                                                 
let verify_commands commands =
  let rec aux variables = function
    | [] -> None  (* If everything goes right *)
    | cmd :: rest_cmds ->
       begin match cmd with
       | Sample_cmd name ->
          if L.mem variables name then already_exists name
          else aux (name :: variables) rest_cmds
                   
       | F_cmd (name, (var, _)) ->
          if not (L.mem variables var) then not_defined var
          else if L.mem variables name then already_exists name
          else aux (name :: variables) rest_cmds
                   
       | R_cmd (names, vars) ->
          begin match L.find vars ~f:(fun v -> not (L.mem variables v)) with
          | Some var -> not_defined var
          | None ->
             begin match L.find vars ~f:(fun v -> not (L.mem variables v)) with
             | Some name -> already_exists name
             | None -> aux (names @ variables) rest_cmds
             end
          end
            
       | XOR_cmd (name, vars) ->
          begin match L.find vars ~f:(fun v -> not (L.mem variables v)) with
          | Some var -> not_defined var
          | None -> if L.mem variables name then already_exists name
                    else aux (name :: variables) rest_cmds
          end

       | Check (var1, _, var2) ->
          if not (L.mem variables var1) then not_defined var1
          else if not (L.mem variables var2) then not_defined var2
          else aux variables rest_cmds
       end
  in
  aux [] commands
     
let assert_commands commands =
  match verify_commands commands with
  | None -> ()
  | Some msg -> failwith msg

let test () =
  let commands = [ Sample_cmd ("x1"); XOR_cmd("x2", ["x1";"x3"]) ] in
  assert_commands commands;
  F.printf "hola\n"

                   
