open Hw1_reduction
open Hw1
open Printf

let test_free_vars = ["\\x.y z t"; "(\\x.x) x"];;

let print_string_list = List.iter (printf "%s\n") 

let test_free_to_subst = [("\\t.(y z) t", "\\x.y z t", "y"); ("x (x x)", "(\\y.\\x.x y) \\t.x", "y")];;
let () = 
    List.fold_left (fun _ s -> 
        printf "free vars of term %s\n" s; print_string_list (free_vars (lambda_of_string s))
    ) () test_free_vars;
    List.fold_left (fun _ (what, where, var) -> 
        printf "is %s free to substitute %s in %s: %B\n" what var where (free_to_subst (lambda_of_string what) (lambda_of_string where) var)
    ) () test_free_to_subst;
    let test = "(\\n.\\f.\\x.n (\\g.\\h.h (g f)) (\\u.x) (\\u.u)) (\\f.\\x.f (f (f x)))" in
    printf "%s\n" (test |>  lambda_of_string |> normal_beta_reduction |> string_of_lambda)
    ;
    let w = lambda_of_string "\\x.x x" in
    let i = lambda_of_string "\\x.x" in
    let k = lambda_of_string "\\x.\\y.x" in
    let s = lambda_of_string "\\x.\\y.\\z.x z (y z)" in
    (* let t = lambda_of_string "\\x.\\y.\\z.x z y" in *)
    let fls = lambda_of_string "\\x.\\y.y" in
    let vara = Hw1.Var "a" in
    (* let varb = Hw1.Var "b" in *)
    let neg = Abs ("a", App (App (vara, fls), k)) in
    (* let xor = Abs ("a", Abs ("b", App (App (vara, App (neg, varb)), varb))) in *)
    let test = [App (App (i, i), i); App (w, i); App (App (s, k), k) ; App (neg, fls); App (neg, k);
    lambda_of_string "(\\n.\\f.\\x.n (\\g.\\h.h (g f)) (\\u.x) (\\u.u)) (\\f.\\x.f (f (f x)))
"] 
    in 
    List.iter (fun term -> 
                            printf "Term: %s\n" (string_of_lambda term);
                            printf "Normal form: %s\n" (term |> reduce_to_normal_form |> string_of_lambda)
                            ) test
    ;;