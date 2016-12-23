(* Defining attackers *)

open Core_kernel.Std
open Abbrevs
open Util
open Expressions
       
(* ** Attack commands *)

type eq = Eq | Ineq

let eq_to_string = function
  | Eq   -> "="
  | Ineq -> "<>"
                 
type block_cipher = {
    n_in   : int;
    n_out  : int;
    cipher : expression list -> expression list                 (* inputs * outputs *)
  }
                      
type command =
  | Sample_cmd of string
  | F_cmd      of string * (string * int)                       (*    output * (input * id)     *)
  | R_cmd      of (string list) * block_cipher * (string list)  (*    outputs * cipher * inputs *)
  | XOR_cmd    of string * (string list)                        (*    output * inputs           *)
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
                   
       | R_cmd (names, cipher, vars) ->
          begin match L.find vars ~f:(fun v -> not (L.mem variables v)) with
          | Some var -> not_defined var
          | None ->
             begin match L.find vars ~f:(fun v -> not (L.mem variables v)) with
             | Some name -> already_exists name
             | None ->
                if L.length vars <> cipher.n_in then Some "Wrong number of cipher inputs"
                else if L.length names <> cipher.n_out then Some "Wrong number of cipher outputs"
                else aux (names @ variables) rest_cmds
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

let inline_adversary ~real commands =
  let rec aux expressions equations = function
    | [] -> expressions, equations
    | cmd :: rest_cmds ->
       begin match cmd with
       | Sample_cmd name -> aux (Map.add expressions ~key:name ~data:(Leaf name)) equations rest_cmds
       | F_cmd (name, (var, id)) -> aux (Map.add expressions ~key:name ~data:(F(Map.find_exn expressions var, id))) equations rest_cmds
       | R_cmd (names, cipher, vars) ->
          let new_variables =
            let vars = L.map vars ~f:(fun v -> Map.find_exn expressions v) in
            if real then cipher.cipher vars
            else L.map (range 0 (L.length names)) ~f:(fun i -> Rand (i, vars))
          in
          let expressions' =
            L.fold_left (L.zip_exn names new_variables)
                   ~init:expressions
                   ~f:(fun emap (name,var) -> Map.add emap ~key:name ~data:var )
          in
          aux expressions' equations rest_cmds
            
       | XOR_cmd (name, vars) ->
          let new_variables = L.map vars ~f:(fun v -> Map.find_exn expressions v) in
          let new_expression =
            L.fold_left (L.tl_exn new_variables)
                   ~init:(L.hd_exn new_variables)
                   ~f:(fun expr v -> XOR(expr, v))
          in
          aux (Map.add expressions ~key:name ~data:(simplify_expr new_expression) ) equations rest_cmds
       | Check (var1, eq, var2) ->
          let expr = simplify_expr (XOR(Map.find_exn expressions var1, Map.find_exn expressions var2)) in
          F.printf "  %a\n" pp_expr expr;
          let satisfied =
            begin match eq, expr with
            | Eq, Zero   -> true
            | Eq, _      -> false
            | Ineq, Zero -> false
            | Ineq, _    -> true
            end
          in
          aux expressions (equations @ [(satisfied, var1, eq, var2)]) rest_cmds
       end
  in
  assert_commands commands;
  aux String.Map.empty [] commands

let rec print_inline_output = function  
  | [] -> ()
  | (b, var1, eq, var2) :: rest ->
     F.printf "%b -> %s %s %s\n" b var1 (eq_to_string eq) var2;
     print_inline_output rest

                   
