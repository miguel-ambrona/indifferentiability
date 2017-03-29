(* Equations solver *)

open Core_kernel.Std
open Abbrevs
open Util
open Expressions
open Feistel

type equation = expression                   (* The expr equals zero *)
type solution = expression String.Map.t      (* atom -> expression *)
type conjunction = solution * equation list * ((expression list * bool) String.Map.t)
                                             (* solution * equations * (atom -> forbidden terms * forbidden recursion) *)
type disjunction = conjunction list

let string_of_equation = string_of_expr
let string_of_solution sol =
  let string_of_term (s,e) = s ^ " -> " ^ (string_of_expr e) in
  Map.to_alist sol |> (string_of_list "\n" string_of_term)
  
let string_of_conjunction ((_solution, equations, forbidden) : conjunction) =
  if L.length equations = 0 then "T"
  else
    (string_of_list " = 0 /\\ \n" string_of_equation equations) ^ " = 0\n" ^
      (L.fold_left (Map.to_alist forbidden)
                   ~init:""
                   ~f:(fun str (s, (exprs,r)) ->
                     str ^ s ^ " does not contain " ^ (string_of_list ", " string_of_equation exprs)
                     ^ (if r then ". No recursion\n" else "Recursion\n")
                   )
      )

let string_of_disjunction disjunction =
  if L.length disjunction = 0 then "T"
  else string_of_list "\n   \\/ \n\n" string_of_conjunction disjunction

let pp_solution _fmt sol = F.printf "%s" (string_of_solution sol)
let pp_conjunction _fmt conj = F.printf "%s" (string_of_conjunction conj)
let pp_disjunction _fmt disj = F.printf "%s" (string_of_disjunction disj)

let rec is_leaf_in_expr (a : string) (e : expression) =
  match e with
  | Zero | VAR _ -> false
  | Leaf s -> s = a
  | F(e', _, _) -> is_leaf_in_expr a e'
  | Rand(_, list, _) -> L.exists list ~f:(is_leaf_in_expr a )
  | XOR(e1,e2) -> (is_leaf_in_expr a e1) || (is_leaf_in_expr a e2)

let substitute_in_conj (a : string) (e : expression) ((solution, equations, forbidden) : conjunction) : conjunction =
  (if is_leaf_in_expr a e then failwith (a ^ " appears in " ^ (string_of_expr e)));
  (match Map.find forbidden a with
   | None -> ()
   | Some (l,_) ->
      let e_list = expr_to_xor_list e in
      if L.exists l ~f:(fun e1 -> L.exists e_list ~f:(fun e2 -> equal_expr e1 e2)) then
        failwith (a ^ " is being subsituted by a forbidden term")
      else ()
  );
  let (strings, solution_exprs) = Map.to_alist solution |> L.unzip in
  let solution_exprs = L.map solution_exprs ~f:(substitute_expr ~old:(Leaf a) ~by:e ) in
  let up_solution = String.Map.of_alist_exn (L.zip_exn strings solution_exprs) in
  
  let up_equations = L.map equations ~f:(substitute_expr ~old:(Leaf a) ~by:e ) in
  
  let (strings, forbidden_lists) = Map.to_alist forbidden |> L.unzip in
  let forbidden_lists = L.map forbidden_lists ~f:(fun (l,r) -> L.map l ~f:(substitute_expr ~old:(Leaf a) ~by:e ), r) in
  let up_forbidden = String.Map.of_alist_exn (L.zip_exn strings forbidden_lists) in 
  (up_solution, up_equations, up_forbidden)

let rearrange_in_groups list_of_exprs =
  let rec aux groups = function
    | [] -> groups
    | t :: rest ->
       let up_groups =
         begin match t with
         | Leaf _ -> Map.change groups (-1) ~f:(function None -> Some [t] | Some l -> Some (t :: l))
         | F(_,i,_) ->
            if i = (-1) then assert false
            else Map.change groups i ~f:(function None -> Some [t] | Some l -> Some (t :: l))
         | _ -> assert false
         end
       in
       aux up_groups rest
  in
  aux Int.Map.empty list_of_exprs

      (*
let get_rid_of_leaf (leaf : string) (e : expression) =
  (*
    This function takes an expression and produces all possible cases of restriccions
    that make 'leaf' disappear from the expression.
    Example:
             leaf: x        e: F(x) + F(F(x) + y) + z
 
    will result into
       * F(x) = 0       /\  e = F(y) + z
       * x = F(x) + y   /\  e = z
       * z -> z' + F(x) + F(F(x) + y)  /\  e = z'

    It returns a list of cases, where very case has:
      - Updated e expression
      - Possible new equations
      - String mapping from variables to other expressions.
  *)
  let rec aux leaves_map = function
    | Zero -> [(Zero, [], leaves_map)]
    | F(e') ->
       *)

      
let solve_conjunction ((partial_sol, equations, forbidden) : conjunction) =
  let rec aux (solution, previous_eqs, up_forbidden) = function
    | [] -> (Some (solution, previous_eqs, up_forbidden), [])
    | eq :: rest_eqs ->
       let eq = full_simplify eq in
       begin match eq with
       | Zero -> aux (solution, previous_eqs, up_forbidden) rest_eqs
       | F(_) -> (None, []) (* Infeasible *)
       | Leaf (a) ->
          let up_solution = Map.change solution a ~f:(function _ -> Some Zero) in
          (None, [substitute_in_conj a Zero (up_solution, previous_eqs @ rest_eqs, up_forbidden)])
       | XOR(Leaf a1, Leaf a2) ->
          let up_solution = Map.change solution a2 ~f:(function _ -> Some (Leaf a1)) in
          let a2_forb, r2 = match Map.find up_forbidden a2 with | None -> ([],false) | Some a -> a in
          let up_forbidden = Map.change up_forbidden a1 ~f:(function None -> if a2_forb = [] then None else Some (a2_forb,false)
                                                                   | Some (forb,r) -> Some (a2_forb @ forb,r)) in
          (None, [substitute_in_conj a2 (Leaf a1) (up_solution, previous_eqs @ rest_eqs, up_forbidden)])
       | XOR(_,_) ->
          let xor_terms = expr_to_xor_list eq in
          let groups = rearrange_in_groups xor_terms in
          let non_leaves = L.filter xor_terms ~f:(function Leaf _ -> false | _ -> true) in
          let up_forbidden =
            L.fold_left (match Map.find groups (-1) with | None -> [] | Some l -> l)
                  ~init:up_forbidden
                  ~f:(fun forb leaf_term ->
                    let a = begin match leaf_term with | Leaf a -> a | _ -> assert false end in
                    L.fold_left non_leaves ~init:forb
                       ~f:(fun up_forb t ->
                               if is_leaf_in_expr a t then Map.change up_forb a ~f:(function None -> Some [t] | Some l -> Some (t :: l))
                               else up_forb
                       )
                  )
          in
          begin match Map.keys groups with
          | [] -> assert false
          | k :: [] when k = (-1) -> aux (solution, previous_eqs @ [eq], up_forbidden) rest_eqs
          | _ as keys ->
             let leaves = begin match Map.find groups (-1) with | None -> [] | Some l -> l end in
             let f k = (* Check if every leaf has forbidden every k_term *)
               if k = (-1) then false
               else
                 let k_terms = Map.find_exn groups k in
                 not (L.exists leaves
                         ~f:(function
                             | Leaf a -> L.exists k_terms
                                         ~f:(fun t -> not (L.mem (match Map.find up_forbidden a with | None -> [] | Some l -> l) t ~equal:equal_expr ))
                             | _ -> assert false
                            )
                     )
             in
             begin match L.find keys ~f with
             | Some k ->
                let k_terms = Map.find_exn groups k in
                if (L.length k_terms)%2 = 1 then (None, []) (* Infeasible *)
                else
                  let up_eq =
                    L.map (L.filter keys ~f:(fun k' -> k' <> k)) ~f:(fun k' -> Map.find_exn groups k')
                    |> L.concat
                    |> xor_list_to_expr
                  in
                  let pairs = split_in_all_pairs k_terms in
                  let new_conjs =
                    L.map pairs
                       ~f:(fun pairs_list ->
                         solution,
                         previous_eqs @ [up_eq] @
                           (L.map pairs_list
                                  ~f:(function
                                      | F(e1,_,_),F(e2,_,_) -> XOR(e1,e2) |> full_simplify
                                      | _ -> assert false
                                     )
                           ) @ rest_eqs,
                         up_forbidden
                       )
                  in
                  (None, new_conjs)
             | None ->
                let k' = L.find_exn keys ~f:(fun k -> k <> (-1) && not (f k)) in
                let k'_terms = Map.find_exn groups k' in
                let leaf' = (* FIXME: Do this command and next one in one single instruction *)
                  L.find_exn leaves
                      ~f:(function
                          | Leaf a -> L.exists k'_terms
                                        ~f:(fun t -> not (L.mem (match Map.find up_forbidden a with | None -> [] | Some l -> l) t ~equal:equal_expr ))
                          | _ -> assert false
                         )
                  |> (function | Leaf a -> a | _ -> assert false)
                in
                let t' = L.find_exn k'_terms ~f:(fun t -> not (L.mem (match Map.find up_forbidden leaf' with | None -> [] | Some l -> l) t ~equal:equal_expr )) in
                let forbidden1 = Map.change up_forbidden leaf' ~f:(function None -> Some [t'] | Some forb -> Some (t' :: forb) ) in
                let conj1 = solution, previous_eqs @ [eq] @ rest_eqs, forbidden1 in
                let new_name = leaf' ^ "~" in
                let forbidden2 =
                  begin match Map.find forbidden1 leaf' with
                  | None -> assert false
                  | Some forb -> Map.add up_forbidden ~key:new_name ~data:forb
                  end
                in
                let new_expr = XOR(Leaf (leaf' ^ "~"), t') |> full_simplify in
                let up_solution = Map.change solution leaf' ~f:(function _ -> Some new_expr) in
                let partial_conj2 = (up_solution, previous_eqs @ [eq] @ rest_eqs, forbidden2) in
                let conj2 = substitute_in_conj leaf' new_expr partial_conj2 in
                (None, [conj1; conj2])
             end
          end
       | VAR _ | Rand _ -> assert false
       end
  in
  aux (partial_sol, [], forbidden) equations

let equal_terms sol a1 a2 =
  let xor1 = match Map.find sol a1 with | None -> Leaf a1 | Some e -> (e |> full_simplify) in
  let xor2 = match Map.find sol a2 with | None -> Leaf a2 | Some e -> (e |> full_simplify) in
  equal_expr xor1 xor2

let equal_pair sol (a1,b1) (a2,b2) =
  if equal_terms sol a1 a2 then equal_terms sol b1 b2
  else false
      
let solve_system (pairs : (string * string) list) (system : disjunction) =
  let rec aux sol_system =
    (*L.iter sol_system ~f:(fun conj -> F.printf "%a\n" pp_conjunction conj);
    F.printf "-------------------------------\n\n\n";
    F.print_flush();*)
    match sol_system with
    | [] -> None
    | (sol, _, _) as conj :: rest_conjs ->
       if exists_duplicate ~equal:(equal_pair sol) pairs then aux rest_conjs (* Duplication violation *)
       else
         begin match solve_conjunction conj with
         | (Some s, _) -> Some s
         | (None, conjs2) -> aux (conjs2 @ rest_conjs)
         end
  in
  aux system
      
let test () =
  let x0 = Leaf "x0" in
  let x1 = Leaf "x1" in
  let x0' = Leaf "x0'" in
  let x1' = Leaf "x1'" in
  let x0'' = Leaf "x0''" in
  let x1'' = Leaf "x1''" in
  let x0''' = Leaf "x0'''" in
  let x1''' = Leaf "x1'''" in

  let _, x5 = feistel_enc x0 x1 4 in
  let _, x5' = feistel_enc x0' x1' 4 in
  let _, x5'' = feistel_enc x0'' x1'' 4 in
  let _, x5''' = feistel_enc x0''' x1''' 4 in

  let xor_x1 = full_simplify (XOR(x1, XOR(x1',XOR(x1'',x1''')))) in
  let xor_x5 = full_simplify (XOR(x5, XOR(x5',XOR(x5'',x5''')))) in
  let pairs = L.map [(x0,x1); (x0',x1');(x0'',x1''); (x0''',x1''')] ~f:(function | (Leaf a, Leaf b) -> (a,b) | _ -> assert false) in
                     
  let eq1 = (String.Map.empty, [xor_x1; xor_x5], String.Map.empty) in
  let system = [eq1] in
  F.printf "%a\n" pp_disjunction system;

  match solve_system pairs system with
  | None   -> F.printf "No solution\n"
  | Some conj ->
     let (s,_,_) = conj in
     F.printf "%a\n" pp_conjunction conj;
     F.printf "%a\n" pp_solution s;
     ()

(*
       F2(F1(x1) + x0) +
       F2(F1(x1') + x0') +
       F2(F1(x1'') + x0'') +
       F2(F1(x1''') + x0''') +
       F4(F1(x1) + F3(F2(F1(x1) + x0) + x1) + x0) +
       F4(F1(x1') + F3(F2(F1(x1') + x0') + x1') + x0') +
       F4(F1(x1'') + F3(F2(F1(x1'') + x0'') + x1'') + x0'') +
       F4(F1(x1''') + F3(F2(F1(x1''') + x0''') + x1''') + x0''') +
       x1 + x1' + x1'' + x1''' = 0
 *)
       
