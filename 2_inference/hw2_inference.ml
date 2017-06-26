open Hw1_reduction
open Hw2_unify
open Hw1
open Printf 

module String_map = Map.Make (String)

module String_set = Set.Make (String)

type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type
type inference_result = ((string * simp_type) list * simp_type) option
type hm_type = HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type

type hm_lambda = HM_Var of string | HM_Abs of string * lambda | HM_App of lambda * lambda | HM_Let of string * lambda * lambda


let rec string_of_type tp =
    match tp with
    | S_Elem x -> x
    | S_Arrow (p, q) -> sprintf "(%s) -> %s" (string_of_type p) (string_of_type q) 
;;



let rename_lambda term =
    let fv = free_vars term in
    let base' = List.fold_left (fun longest_var var -> 
                                    if String.length longest_var < String.length var 
                                        then var
                                        else longest_var) "" fv in 
    let base = if String.length base' = 0 then "x" else base' in
    let cnt = ref 0 in 
    let rec helper t bound = 
        match t with
        | Hw1.Var x -> let x' = if String_map.mem x bound then String_map.find x bound else x
                                in Hw1.Var x'
        | App (p, q) -> App (helper p bound, helper q bound)
        | Abs (var, body) -> cnt := !cnt + 1;
                             let var' = (base ^ (string_of_int !cnt)) in
                            let bound' = String_map.add var var' bound in
            Abs (var', helper body bound') in
    helper term String_map.empty;;


let rec alg_term_to_type term = 
    match term with
    | Hw2_unify.Var x -> S_Elem x
    | Fun (_, args) -> S_Arrow ((alg_term_to_type (List.nth args 0)), 
                            alg_term_to_type (List.nth args 1));;

let lambda_to_system (term : lambda) : ((algebraic_term * algebraic_term) list) * algebraic_term * (string list) =
    let cnt = ref 0 in
    let impl l r = Fun ("Impl", [l; r]) in
    let rec helper t =
        match t with
        | Hw1.Var x -> 
            ([], Hw2_unify.Var ("t" ^ x), String_set.singleton x)
        | App (p, q) -> cnt := !cnt + 1; 
                        let new_type = Hw2_unify.Var ("t" ^ (string_of_int !cnt)) in
                        let (sys_p, type_p, vars_p) = helper p in
                        let (sys_q, type_q, vars_q) = helper q in
                        ((type_p, impl type_q new_type) 
                            :: (List.rev_append  sys_p sys_q), new_type, 
                                    String_set.union vars_p vars_q)
        | Abs (x, body) -> 
                        let (sys, tp, vars) = helper body in
                        (sys, impl (Var ("t" ^ x)) tp, String_set.add x vars)
    in let (sys, tp, vars) = helper term in
    (sys, tp, String_set.elements vars) 
    ;;

let infer_simp_type term =
    let (sys, tp, all_vars) = lambda_to_system (rename_lambda term) in
    let sol = solve_system sys in
    match sol with
    | None -> None
    | Some sub ->   let var_types = List.rev_map (fun var -> (var, apply_substitution sub (Hw2_unify.Var ("t" ^ var)) |> alg_term_to_type) ) all_vars in
                    let whole_type = alg_term_to_type (apply_substitution sub tp) in
                    Some (var_types, whole_type);;


let print_infer_res res =
    match res with
    | None -> printf "No type\n"
    | Some (var_types, tp) -> 
            printf "Types of vars\n";
            List.iter (fun (v, t) -> printf "%s : %s\n" v (string_of_type t)) var_types;
            printf "Whole term: %s\n" (string_of_type tp)
        ;;

let () = 
    let i = Hw1.lambda_of_string "\\x.x" in
    let k = Hw1.lambda_of_string "\\x.\\y.x" in
    let s = Hw1.lambda_of_string "\\x.\\y.\\z.x z (y z)" in
    let t = Hw1.lambda_of_string "\\x.\\y.\\z.x z y" in
    let fls = Hw1.lambda_of_string "\\x.\\y.y" in
    let vara = Hw1.Var "a" in
    let varb = Hw1.Var "b" in
    let neg = Abs ("a", App (App (vara, fls), k)) in
    let xor = Abs ("a", Abs ("b", App (App (vara, App (neg, varb)), varb))) in
    let test = [App (App (k, vara), varb); App (vara, s); i; k; s; t; App (s, k); App (App (s, k), k); App (i, App (i, s)); neg; xor] in
    List.iter (fun item -> printf "Term: %s\n" (rename_lambda  item |> Hw1.string_of_lambda);
                         item |> infer_simp_type |> print_infer_res ) test;;
