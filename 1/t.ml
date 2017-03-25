open Hw1;;
open Printf;;

(* print_int (int_of_peano (S (S (Z))));;

print_string "\n";;
 *)
let three = S (S (S Z));;


printf "%d\n" (int_of_peano ( sub three (S (S Z))   ));;



printf "%d\n" (int_of_peano (mul three (sub three (S Z))));;


printf "%s\n" (get_var (fst (parse_var "a}" 0)));;
printf "%s\n" (Hw1.string_of_lambda (fst (parse_arg "x" 0) ));;

printf "%d\n" (helper_parse_var "x y1" 0 false);;

printf "%d\n" (snd (parse_var "x y1" 0));;

(* printf "%d\n" (snd (helper_parse_var "x y1" 0 ));; *)


printf "%s\n" (Hw1.string_of_lambda (Hw1.lambda_of_string "(x)"));;

let res = parse_app "x y1" 0;;
printf "%s\n" (Hw1.string_of_lambda (fst res) );;

printf "%s\n" (string_of_lambda (App (Abs ("x", Var "x"), Var "y")));;

printf "%d\n" (snd res);;

let test = ["\\x.\\y.x y z234 y"; "\\x.\\y.x (y z234 y)"; ""];;
List.fold_left (fun _ t -> printf "%s\n" (string_of_lambda (Hw1.lambda_of_string t) )) () test;;


let print_int_list l = List.fold_left (fun _ x -> printf "%d " x) () l;;
print_int_list (merge [1; 3] [2; 4]);;
print_int_list [1;2;3;4];;

print_int_list (fst (split [4;1;3;2] 2));;

print_int_list (merge_sort [4;1;3;2]);;
(* printf "%s\n" (Hw1.string_of_lambda (Hw1.lambda_of_string "\\x.\\y.x y z234 y"));; *)
