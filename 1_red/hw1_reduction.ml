open Hw1
open Common
open Printf
module String_set = Set.Make (String);;

module String_map = Map.Make (String);;

type indexed_lambda = IVar of int | IApp of (indexed_lambda * indexed_lambda) | IAbs of indexed_lambda;;


let rec set_of_free_vars t = match t with
    | Var x -> String_set.singleton x
    | App (p, q) -> String_set.union (set_of_free_vars p) (set_of_free_vars q)
    | Abs (x, body) -> String_set.remove x (set_of_free_vars body);;


let rec free_to_subst what where var = 
    let fv = set_of_free_vars what in 
        match where with
            | Var x -> true
            | App (p, q) -> (free_to_subst what p var) && (free_to_subst what q var)
            | Abs (y, body) -> var = y || (not (String_set.mem y fv)) && (free_to_subst what body var);;


let rec free_vars term = String_set.elements (set_of_free_vars term)

(* fv is not necessarily equal to (free_vars term), it is useful when we convert several terms 
    with a united set of free vars *)
let rec to_indexed_lambda fv term = 
    let free_var_to_index = 
        List.fold_left (fun m var -> String_map.add var ((String_map.cardinal m) + 1) m)
                                                            String_map.empty fv in
    let rec helper t bound_to_depth depth =
        match t with
            | Var x -> IVar (if String_map.mem x bound_to_depth 
                                then depth - (String_map.find x bound_to_depth) + 1
                                else (String_map.find x free_var_to_index) + depth) 
            | App (p, q) -> IApp ((helper p bound_to_depth depth), (helper q bound_to_depth depth))
            | Abs (y, body) ->  IAbs (helper body (String_map.add y (depth + 1) bound_to_depth)
                                                                                    (depth + 1)) in
            helper term String_map.empty 0;;

let rec from_indexed_lambda fv term = 
    let base = List.fold_left (fun longest_var var -> if String.length longest_var < String.length var 
                                                            then var
                                                            else longest_var) "" fv in 
    let fv_array = Array.of_list fv in
    let rec helper t depth =
        match t with
        | IAbs body -> let var = base ^ (string_of_int (depth + 1)) in
            Abs (var, (helper body (depth + 1) ))
        | IApp (p, q) -> App (helper p depth, helper q depth)
        | IVar i -> let var = if i >= depth + 1 
                                    then Array.get fv_array (i - depth - 1)
                                    else base ^ (string_of_int (depth - i + 1)) in
            Var var in
        helper term 0;;

let rec string_of_indexed_lambda iterm = 
    match iterm with
    | IAbs body -> "\\" ^ (string_of_indexed_lambda body) 
    | IApp (p, q)  -> "(" ^ (string_of_indexed_lambda p) ^ ") (" ^ (string_of_indexed_lambda q) ^ ")"
    | IVar i -> string_of_int i;;


let rec subst what where var = failwith "";;

let rec subst_indexed where what = 
    let shift term delta = 
        let rec helper t depth = 
            match t with
            | IVar i -> if i > depth then IVar (i + delta) else IVar i
            | IApp (p, q) -> IApp (helper p depth, helper q depth)
            | IAbs body -> IAbs (helper body (depth + 1)) in
        helper term 0 in
    let rec helper i_term depth subst =
        match i_term with
        | IVar i -> if i = depth then (shift subst depth) else IVar i  
        | IApp (p, q) -> IApp ((helper p depth subst), (helper q depth subst))
        | IAbs body -> IAbs (helper body (depth + 1) subst) in
    helper where 1 what;;

(* (Some res) if term has been reduced to res, None otherwise *)
let rec indexed_lambda_reduction (t : indexed_lambda) : indexed_lambda option = 
    match t with
    | IApp (IAbs body, q) -> Some (subst_indexed body q)
    | IApp (p, q) -> 
        let res_p = indexed_lambda_reduction p in
            (match res_p with
            | Some x -> Some (IApp (x, q))
            | None -> let res_q = indexed_lambda_reduction q in
                (match res_q with
                | Some x -> Some (IApp (p, x))
                | None -> None))
    | IAbs body -> 
        let reduced = indexed_lambda_reduction body in
        (match reduced with
        | Some x -> Some (IAbs x)
        | _ -> None)
    | IVar i -> None;;


let normal_beta_reduction term = 
    let fv = free_vars term in
    let res = term |> to_indexed_lambda fv |> indexed_lambda_reduction in
    match res with 
        | None -> failwith "Term is in normal form"
        | Some x -> from_indexed_lambda fv x;;

let rec is_alpha_equivalent term term' = 
    let fv = String_set.elements 
        ( String_set.union (set_of_free_vars term) (set_of_free_vars term')) in
            to_indexed_lambda fv term = to_indexed_lambda fv term';;

let is_normal_form term = 
    let is_none x = 
        match x with
        | None -> true
        | _ -> false in
    term |> to_indexed_lambda (free_vars term) |> indexed_lambda_reduction |> is_none;;

let () = 
    let test_str = "(\\x.x \\x.x) (y \\y.x z (\\y.y))" in
    let test = lambda_of_string test_str in
    let test' = lambda_of_string  "(\\x1.x1 \\x.x) (y \\y1.x z (\\y.y))" in
    let fv = free_vars test in
    let after = test |> to_indexed_lambda fv |> from_indexed_lambda fv in
    printf "before: %s\nafter: %s\n" test_str (string_of_lambda after);
    printf "%B\n" (is_alpha_equivalent test test');
    print_string_list (free_vars test);