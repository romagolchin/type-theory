open Hw2_inference
open Hw1
open Printf

let rec string_of_type tp =
    match tp with
    | S_Elem x -> x
    | S_Arrow (p, q) -> sprintf "(%s) -> %s" (string_of_type p) (string_of_type q) 
;;


let print_infer_res res =
    match res with
    | None -> printf "No type\n"
    | Some (var_types, tp) -> 
            printf "Types of vars\n";
            List.iter (fun (v, t) -> printf "%s : %s\n" v (string_of_type t)) var_types;
            printf "Whole term: %s\n" (string_of_type tp)
        ;;


let rec string_of_hmt hmt = 
    match hmt with
    | HM_Elem v -> v
    | HM_Arrow(hmt1, hmt2) -> sprintf "(%s) -> %s" (string_of_hmt hmt1) (string_of_hmt hmt2)
    | HM_ForAll(v, hmt) -> sprintf "@%s(%s)" v (string_of_hmt hmt);;

let rec string_of_hml hml =
    match hml with 
    | HM_Var v -> v
    | HM_Abs(v, hml) -> sprintf "\\%s.(%s)" v (string_of_hml hml)
    | HM_App(hml1, hml2) -> sprintf "(%s %s)" (string_of_hml hml1) (string_of_hml hml2)
    | HM_Let(v, hml1, hml2) -> sprintf "let %s = %s in %s " v (string_of_hml hml1) (string_of_hml hml2)

let hm_test hml =
    printf "\nTest: %s\n" (string_of_hml hml);
    match (Hw2_inference.algorithm_w hml) with
        | None -> printf "W failed to infer type\n"
        | Some (cont, hmt) -> 
            (
            printf "Inferred type: %s\n" (string_of_hmt hmt);
            List.iter (fun (v, hmt) -> printf  "%s : %s\n" v (string_of_hmt hmt)) cont;
            printf "\n");; 

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
    let simple_tests = [App (App (k, vara), varb); App (vara, s); i; k; s; t; App (s, k); App (App (s, k), k); App (i, App (i, s)); neg; xor] in
    List.iter (fun item -> printf "Term: %s\n" (item |> Hw1.string_of_lambda);
                         item |> infer_simp_type |> print_infer_res ) simple_tests;
    let x = HM_Var "x" in
    let id = HM_Var "id" in
    let i_comb = HM_Abs ("x", x) in
    let tt = [
        HM_Let ("id", i_comb, HM_Abs ("f", (HM_Abs ("x", HM_App (id, HM_App (id, x))))) );
        HM_Let ("id", i_comb, HM_Abs ("f", (HM_Abs ("x", HM_App (HM_App (id, HM_Var "f"), HM_App(HM_App (id, x), HM_App (id, x)) )))))
    ] in 
    List.iter (fun x -> hm_test x) tt;;