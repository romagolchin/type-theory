open Common
open Hw1_reduction
open Hw1
open Printf

let test_free_vars = ["\\x.y z t"; "(\\x.x) x"];;

let test_free_to_subst = [("\\t.(y z) t", "\\x.y z t", "y"); ("x (x x)", "(\\y.\\x.x y) \\t.x", "y")];;
let () = 
    List.fold_left (fun _ s -> 
        printf "free vars of term %s\n" s; print_string_list (free_vars (lambda_of_string s))
    ) () test_free_vars;
    List.fold_left (fun _ (what, where, var) -> 
        printf "is %s free to substitute %s in %s: %B\n" what var where (free_to_subst (lambda_of_string what) (lambda_of_string where) var)
    ) () test_free_to_subst;;