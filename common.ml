open Printf
type lambda = Var of string | Abs of string * lambda | App of lambda * lambda;;

type peano = Z | S of peano;;


let print_generic_list fmt l = List.fold_left (fun _ x -> printf fmt x) () l; printf "\n";;

let print_int_list l = print_generic_list "%s ";;

let print_string_list = print_generic_list "%s ";;