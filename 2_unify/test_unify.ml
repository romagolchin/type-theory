open Printf
open Hw1
open Hw2_unify
open Hw1_reduction

module String_map = Map.Make (String);;


let rec string_of_alg_term term = 
    match term with
    | Var x -> x
    | Fun (f, args) -> 
            if f = "Impl" 
                then "(" ^ (string_of_alg_term (List.nth args 0)) ^ ") -> " ^ (string_of_alg_term (List.nth args 1))
            else let len = List.length args in
            f ^ " " ^ (fst (List.fold_left (fun (s, i) a -> 
                                let str = "(" ^ s ^ (string_of_alg_term a) ^ ")" in
                                if i <> len - 1 
                                    then (str ^ " ", i + 1)
                                else (str, i + 1)) ("", 0) args));;


let string_of_sys sys = 
    "{\n" ^ (List.fold_left (fun s (lhs, rhs) -> 
                        s ^ (string_of_alg_term lhs) ^ " = " ^ (string_of_alg_term rhs) ^ "\n"  ) "" sys) ^ "}";;


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

let lambda_to_system (term : lambda) : ((algebraic_term * algebraic_term) list) * algebraic_term =
    let cnt = ref 0 in
    let impl l r = Fun ("Impl", [l; r]) in
    let rec helper t =
        match t with
        | Hw1.Var x -> 
            ([], Hw2_unify.Var ("t" ^ x))
        | App (p, q) -> cnt := !cnt + 1; 
                        let new_type = Hw2_unify.Var ("t" ^ (string_of_int !cnt)) in
                        let (sys_p, type_p) = helper p in
                        let (sys_q, type_q) = helper q in
                        ((type_p, impl type_q new_type) 
                            :: (List.rev_append  sys_p sys_q), new_type)
        | Abs (x, body) -> 
                        let res = helper body in
                        (fst res, impl (Var ("t" ^ x)) (snd res))
    in let (sys, tp) = helper term in
    (sys, tp) ;;


let rec print_substitution sub =
    match sub with 
    | [] -> print_string "\n"
    | (h::t) -> print_string ((fst h) ^ " = " ^ (string_of_alg_term (snd h)) ^ "\n"); print_substitution t;; 

let eqt11 = Fun("x", [Var "p1"]), Fun("x", [Var "p2"]) 
let eqt12 = Fun("y", [Var "p2"]), Fun("y", [Var "p4"])
let eqt13 = Fun("z", [Var "p5"]), Fun("z", [Var "p6"])

let eqt21 = Fun("x", [Var "p1"]), Fun("x", [Var "p2"]) 
let eqt22 = Fun("m", [Var "p1"]), Fun("y", [Var "p4"])
let eqt23 = Fun("z", [Var "p5"]), Fun("z", [Var "p6"])

let eqt31 = Fun("x", [Var "p1"]), Fun("x", [Var "p2"]) 
let eqt32 = Fun("y", [Var "p1"]), Fun("y", [Var "p4"])
let eqt33 = Fun("z", [Var "p1"]), Fun("z", [Var "p6"])

let syms = [[eqt11; eqt12; eqt13];
[eqt21; eqt22; eqt23];
[eqt31; eqt32; eqt33]];;

let () =
    (* let w = lambda_of_string "\\x.x x" in *)
    let i = lambda_of_string "\\x.x" in
    let k = lambda_of_string "\\x.\\y.x" in
    let s = lambda_of_string "\\x.\\y.\\z.x z (y z)" in
    let t = lambda_of_string "\\x.\\y.\\z.x z y" in
    let fls = lambda_of_string "\\x.\\y.y" in
    let vara = Hw1.Var "a" in
    let varb = Hw1.Var "b" in
    let neg = Abs ("a", App (App (vara, fls), k)) in
    let xor = Abs ("a", Abs ("b", App (App (vara, App (neg, varb)), varb))) in
    let test = [i; k; s; t; App (s, k); App (App (s, k), k); App (i, App (i, s)); neg; xor] in
    (* let (sys, tp) = lambda_to_system (Abs ("x", Hw1.Var "y")) in *)
    printf "Oktai's \n";
    List.iter (fun sys ->   printf "System:\n%s\n" (string_of_sys sys);
                            let sol = solve_system sys
                            in match sol with
                            | None -> printf "No solution\n"
                            | Some x -> (* print_substitution x; *)
                                (check_solution x sys) |> printf "%B\n") syms;

    printf "Mine \n";
    List.iter (fun comb -> 
                printf "Term: %s\n" (string_of_lambda comb);
                printf "Nice: %s\n" (comb |> rename_lambda |> string_of_lambda);
                let (sys, tp) = comb |> rename_lambda |> lambda_to_system in
                let solution = match (solve_system sys) with
                | Some x -> x
                | _ -> failwith "No solution, no type" in
                let subst_type = apply_substitution solution tp in
                printf "%s\n" (string_of_alg_term subst_type);
                printf "%B\n" (check_solution solution sys);
                (* print_substitution solution; *)
            ) test;;
