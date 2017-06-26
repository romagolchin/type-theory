open String;;
open Char;;

type lambda = Var of string | Abs of string * lambda | App of lambda * lambda
type peano = Z | S of peano


let rec peano_of_int x = if x = 0 then Z else S (peano_of_int (x - 1));;

let rec int_of_peano p = match p with
    Z -> 0
    | S x -> 1 + int_of_peano x;;

let inc x = S x;;
let rec add x = fun y -> match y with
    | Z -> x
    | S t -> inc (add x t);;
let rec mul x = fun y -> match y with
    Z -> Z
    | S t -> add x (mul x t)    ;;
let rec sub x = fun y -> match y with
    | Z -> x
    | S t -> let r = sub x t in match r with
    | Z -> Z
    | S q -> q;;
let rec power x = fun y -> match y with
    | Z -> S Z
    | S t -> mul x (power x t);;
                     
let rev l = List.fold_left (fun xs x -> x :: xs) [] l

let println_string s = print_string (s ^ "\n");;

let println_int x = print_string ((string_of_int x) ^ "\n");;


let lambda = '\\'
let is_alpha c = let cd = code c in cd >= 0x41 && cd <= 0x5a || cd >= 0x61 && cd <= 0x7a;;

let is_digit c = let cd = code c in cd - (code '0') >= 0 && cd - (code '0') <= 9;;

let str_empty s i = i >= String.length s;;
let suf s i = String.sub s i ((String.length s) - i);;
let string_of_char c = String.make 1 c;;

let is_abs x = match x with
    | Abs (_, _) -> true
    | _ -> false

let rec string_of_lambda x = 
    let paren s = "(" ^ s ^ ")" in
    match x with
    | Var s -> s
    | Abs (x, t) -> (string_of_char lambda) ^ x ^ "." ^ (string_of_lambda t)
    | App (p, q) -> let sp = string_of_lambda p in 
                        let sq = string_of_lambda q in 
                            let sq' = match q with
                                | App (_, _) -> paren sq
                                | _ -> sq
                                in match p with 
                                    | Abs (_, _) -> paren sp ^ " " ^ sq'
                                    | App (_, Abs _) -> paren sp ^ " " ^ sq'
                                    | _ -> sp ^ " " ^ sq';;

let get_var l = match l with
    | Var x -> x
    | _ -> failwith "not a variable" 

let rec helper_parse_var s i b =

    if not (str_empty s i) then
        if (not b) 
            then if (is_alpha s.[i]) 
                then helper_parse_var s (i + 1) true
                else failwith ("expected letter at position " ^ (string_of_int i) ^ ", got " ^ (String.sub s i 1))
            else if (is_digit s.[i])
                then helper_parse_var s (i + 1) b
                else i
        else i;;
let parse_var s i =
    let res = helper_parse_var s i false in
    (Var (String.sub s i (res - i)), res);;
        (* else failwith "end of string reached, cannot parse variable" *)


let fail_char s i c = 
    let s' = if str_empty s i 
        then "end of string"
        else String.sub s i 1
    in failwith ("expected " ^ (string_of_char c) ^ " at position " ^ (string_of_int i) ^ ", got " ^ s');;

let rec helper_parse_app acc s i = 
    if (str_empty s i) || (s.[i] != ' ')
        then (acc, i)
        else let res = parse_arg s (i + 1) in let index = snd res in 
                helper_parse_app (App (acc, fst res)) s index

and parse_app s i = 
    let res = parse_arg s i in
        helper_parse_app (fst res) s (snd res)
and parse_arg s i = 
    if (not (str_empty s i)) && s.[i] == lambda 
        then let var = parse_var s (i + 1) in
            if (snd var < String.length s) && s.[snd var] == '.' 
                then let body = parse_app s ((snd var) + 1) in
                    (Abs (get_var (fst var), fst body), snd body) 
                else fail_char s (snd var) '.'
        else if (i < String.length s) && (s.[i] == '(')
            then let res = parse_app s (i + 1) in
                if snd res < String.length s && s.[snd res] == ')' 
                    then (fst res, (snd res) + 1)
                    else  fail_char s (snd res) ')'
            else parse_var s i;;
                
                (* then 
                else failwith "expression from position " ^ (string_of_int i) ^ 
                    " is neither abstraction nor lambda in parentheses" *)
            


let lambda_of_string s = fst (parse_app s 0);;

let rec merge l m = match (l, m) with
    | ([], x) -> x
    | (x, []) -> x
    | (a :: l', b :: m') -> if a <= b 
        then a :: (merge l' (b :: m'))
        else b :: (merge (a :: l') m')

let rec split y n = match y with
    | [] -> ([], [])
    | (x :: xs) -> if n = 0 then ([], (x::xs)) else let res = split xs (n - 1) in (x :: (fst res), snd res )


let rec merge_sort bs = match bs with
    | [] -> []
    | [el] -> [el]
    | _ -> let z = split bs (List.length bs / 2) in merge (merge_sort (fst z)) (merge_sort (snd z))
 (* 

    (\\x.y x (\\x.x)) y
 *)
