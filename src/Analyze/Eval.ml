open Core_kernel.Std
open Abbrevs
open Util
open Expressions
open Attacker

type set =
  | ZO of string

type round = { round_name : string; round_from : set; round_to : set }
               
type eval_state = {
  es_sets : (string * set) list;
  es_round_functions : round list;
  es_oracle_types : (string * int * int) list;  (* name, number of inputs, number of outputs *)
  es_oracles : (string * block_cipher) list;
  es_attacker : command list
}

let empty_eval_state = {
  es_sets = [];
  es_round_functions = [];
  es_oracle_types = [];
  es_oracles = [];
  es_attacker = [];
}

type pseudo_code_cmd =
  | Pseudo_sample of string * string
  | Pseudo_fun of string * (string list) * (string list)
  | Pseudo_xor of string * (string list)
  | Pseudo_check of string * eq * string
  | Pseudo_return of string list
             
type cmd =
  | DefineSet of string * set
  | DefineRounds of (string list) * string * string
  | DefineOracle of string * (string list) * (string list)                                           
  | OracleCode of string * (string list) * (pseudo_code_cmd list)
  | Attacker of pseudo_code_cmd list                             

let get_set sets name =
  match L.find sets ~f:(fun (s,_) -> s = name) with
  | None -> failwith ("Set " ^ name ^ " is not defined")
  | Some (_,set) -> set

let translate_oracle_commands oname inputs estate pseudo_commands =
  let rec aux commands = function
    | [] -> failwith ("Oracle " ^ oname ^ " does not return any value")
    | pseudo_cmd :: rest ->
       begin match pseudo_cmd with
       | Pseudo_sample _ -> failwith "Sampling is not allowed in oracle code"
       | Pseudo_fun (name, inputs, outputs) ->
          let existing_funs = L.map estate.es_round_functions ~f:(fun r -> r.round_name) in
          (if L.mem existing_funs name then () else failwith ("Round function " ^ name ^ " is not defined"));
          (if L.length inputs = 1 then () else failwith ("Round functions take exactly 1 input " ^ (string_of_int (L.length inputs)) ^ " given"));
          (if L.length outputs = 1 then () else failwith ("Round functions return exactly 1 output " ^ (string_of_int (L.length outputs)) ^ " given"));
          aux (commands @ [F_cmd (L.hd_exn outputs, (L.hd_exn inputs, find_position existing_funs ~f:(fun s -> s = name)), Some name )]) rest
       | Pseudo_xor (name, list) -> aux (commands @ [XOR_cmd (name, list)]) rest
       | Pseudo_check _ -> failwith "Checks is not allowed in oracle code"
       | Pseudo_return (returned) -> commands, returned
       end
  in
  let commands, returned = aux [] pseudo_commands in
  let cipher list =
    (if L.length list = L.length inputs then () else failwith "Wrong number of inputs");
    let map = String.Map.of_alist_exn (L.zip_exn inputs list)
              |> Map.add ~key:"0" ~data:Zero
    in
    let expressions, _ = aux_inline_adversary true map [] commands in
    L.map returned ~f:(fun s -> Map.find_exn expressions s)
  in
  { n_in = L.length inputs; n_out = L.length returned; cipher = cipher }
    
let translate_attacker_commands estate pseudo_commands =
  L.map pseudo_commands
    ~f:(function
        | Pseudo_sample (v,s) ->
           begin match L.find estate.es_sets ~f:(fun (name,_) -> name = s) with
           | None -> failwith ("Set " ^ s ^ " is not defined")
           | Some _set -> Sample_cmd v
           end
           
       | Pseudo_fun (name, inputs, outputs) ->
          let existing_funs = L.map estate.es_round_functions ~f:(fun r -> r.round_name) in
          if L.mem existing_funs name then
            let () =
              (if L.length inputs = 1 then () else failwith ("Round functions take exactly 1 input " ^ (string_of_int (L.length inputs)) ^ " given"));
              (if L.length outputs = 1 then () else failwith ("Round functions return exactly 1 output " ^ (string_of_int (L.length outputs)) ^ " given"))
            in
            F_cmd (L.hd_exn outputs, (L.hd_exn inputs, find_position existing_funs ~f:(fun s -> s = name)), Some name )
          else
            begin match L.find estate.es_oracles ~f:(fun (oname, _) -> oname = name) with
            | None -> failwith ("Function " ^ name ^ " is not defined")
            | Some (_,cipher) -> R_cmd (outputs, cipher, inputs, Some name)
            end
                  
       | Pseudo_xor (name, list) -> XOR_cmd (name, list)
       | Pseudo_check (v1,eq,v2) -> Check (v1,eq,v2)
       | Pseudo_return _ -> failwith "Return is not allowed in attacker code"
       )
    
let eval_cmd estate cmd =
  match cmd with
  | DefineSet (name, set) -> { estate with es_sets = estate.es_sets @ [(name,set)] }
                               
  | DefineRounds (names, input, output) ->
     let existing_names = L.map estate.es_round_functions ~f:(fun r -> r.round_name) in
     (begin match L.find names ~f:(fun n -> L.mem existing_names n) with
      | None -> ()
      | Some n -> failwith ("Round function " ^ n ^ " is already defined")
      end);
     let input_set = get_set estate.es_sets input in
     let output_set = get_set estate.es_sets output in
     let rounds = L.map names ~f:(fun s -> { round_name = s; round_from = input_set; round_to = output_set }) in
     { estate with es_round_functions = estate.es_round_functions @ rounds }
       
  | DefineOracle (name, inputs, outputs) ->
     let existing_names = L.map estate.es_oracle_types ~f:(fun (s,_,_) -> s) in
     (if L.mem existing_names name then failwith ("Function " ^ name ^ " is already defined") else ());
     { estate with es_oracle_types = estate.es_oracle_types @ [(name, L.length inputs, L.length outputs)] }

  | OracleCode (name, inputs, pseudo_commands) ->
     { estate with es_oracles = estate.es_oracles @ [(name, translate_oracle_commands name inputs estate pseudo_commands)] }

  | Attacker (pseudo_commands) ->
     (if L.length estate.es_attacker = 0 then () else failwith "An attacker was already defined");
     { estate with es_attacker = translate_attacker_commands estate pseudo_commands }

let eval_cmds cmds =
  let es = L.fold_left cmds ~init:empty_eval_state ~f:eval_cmd in
  es.es_attacker
