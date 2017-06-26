open Hw1
open Common
open Printf
module String_set = Set.Make (String);;

module String_map = Map.Make (String);;

type indexed_lambda = IVar of int | IApp of (indexed_lambda * indexed_lambda) | IAbs of indexed_lambda;;

let is_none x = 
    match x with
    | None -> true
    | _ -> false;;

let rec longest_var t =
    match t with
    | Var x -> x
    | App (p, q) -> let vp = longest_var p in
                    let vq = longest_var q in
                    if String.length vp < String.length vq
                        then vq
                        else vp  
    | Abs (x, p) -> longest_var p ;;

let rec set_of_free_vars t = match t with
    | Var x -> String_set.singleton x
    | App (p, q) -> String_set.union (set_of_free_vars p) (set_of_free_vars q)
    | Abs (x, body) -> String_set.remove x (set_of_free_vars body);;


let rec free_to_subst what where var = 
    let fv = set_of_free_vars what in 
        match where with
            | Var x -> true
            | App (p, q) -> (free_to_subst what p var) && (free_to_subst what q var)
            | Abs (y, body) -> 
                var = y || (not (String_set.mem y fv)) && (free_to_subst what body var);;


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
    let base' = List.fold_left (fun longest_var var -> 
                                    if String.length longest_var < String.length var 
                                        then var
                                        else longest_var) "" fv in 
    let base = if String.length base' = 0 then "x" else base' in
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


let rec subst what where var = 
    match where with
    | Var x -> if x = var then what else Var x
    | App (p, q) -> App (subst what p var, subst what q var)
    | Abs (x, body) -> if x = var then Abs (x, body) else Abs (x, subst what body var);;



(* (Some res) if term has been reduced to res, None otherwise *)
let rec reduce_nice (t : lambda) : lambda option = 
    match t with
    | App (Abs (x, body), q) -> Some (subst q body x)
    | App (p, q) -> 
        let res_p = reduce_nice p in
            (match res_p with
            | Some x -> Some (App (x, q))
            | None -> let res_q = reduce_nice q in
                (match res_q with
                | Some x -> Some (App (p, x))
                | None -> None))
    | Abs (x, body) -> 
        let reduced = reduce_nice body in
        (match reduced with
        | Some r -> Some (Abs (x, r))
        | _ -> None)
    | Var x -> None;;


(* converting to and from indexed_lambda is needed to guarantee that all free vars' names
    are different from those ob bound vars *)
let reduce term = 
    let fv = free_vars term in
    term |> to_indexed_lambda fv |> from_indexed_lambda fv |> reduce_nice;;

let normal_beta_reduction term = 
    let res = reduce term in
    match res with 
        | None -> failwith "Term is in normal form"
        | Some x -> x;;

let rec is_alpha_equivalent term term' = 
    let fv = String_set.elements 
        ( String_set.union (set_of_free_vars term) (set_of_free_vars term')) in
            to_indexed_lambda fv term = to_indexed_lambda fv term';;

let is_normal_form term = term |> reduce |> is_none;;


let cnt = ref 0;;
let get_n_var () = 
    cnt := !cnt + 1;
    ("n_var_" ^ string_of_int !cnt);;


let rename_lambda map term =
    let rec helper t bound = 
        match t with
        | Common.Var x -> let x' = if String_map.mem x bound then String_map.find x bound else x
                                in Common.Var x'
        | App (p, q) -> App (helper p bound, helper q bound)
        | Abs (var, body) ->    let var' = get_n_var () in
                                let bound' = String_map.add var var' bound in
            Abs (var', helper body bound') in
    helper term map;;



type ref_lambda = RVar of string | RApp of (ref_lambda ref * ref_lambda ref)  | RAbs of (string * ref_lambda ref)

let rec to_ref_lambda (t : lambda) : ref_lambda = 
    match t with
        | Var x -> RVar x
        | App (p, q) -> RApp (ref (to_ref_lambda p), ref (to_ref_lambda q))
        | Abs (x, p) -> RAbs (x, ref (to_ref_lambda p)) ;;   

let rec from_ref_lambda (rt : ref_lambda ref) : lambda =
    match !rt with
    | RVar x -> Var x
    | RApp (p, q) -> App (from_ref_lambda p, from_ref_lambda q)
    | RAbs (x, p) -> Abs (x, from_ref_lambda p)

let ($) f g = fun x -> f (g x)

let string_of_ref_lambda = string_of_lambda $ from_ref_lambda 

let reduce_to_normal_form term =
    let rec ref_subst (what : ref_lambda ref)  (where : ref_lambda ref) (var : string) = 
        (* printf "what = %s where = %s var = %s\n" (string_of_ref_lambda what) (string_of_ref_lambda where) var; *)
        match !where with
        | RVar x ->  
            if var = x then where := !what
        | RApp (p, q) ->  ref_subst what p var; ref_subst what q var
        | RAbs (x, p) -> if var <> x then ref_subst what p var
    in
    let rec ref_reduce (rt : ref_lambda ref) : ref_lambda ref option =
        match !rt with
        | RApp ({ contents = RAbs (x, body) }, q) ->
                (* printf "body = %s\n" (body |> from_ref_lambda |> string_of_lambda); *)
                let n_var = get_n_var () in 
                let map = String_map.singleton x n_var in
                rt := to_ref_lambda (rename_lambda map (from_ref_lambda body));              
                (* rt := to_ref_lambda (from_ref_lambda body); *)
                ref_subst q rt n_var;
                (* ref_subst q rt x; *)
                Some rt 
        | RApp (p, q) -> 
            let res_p = ref_reduce p in
                ( match res_p with
                | Some _ -> Some rt 
                | _ -> let res_q = ref_reduce q in
                    ( match res_q with
                    | Some _ -> Some rt
                    | _ -> None

                    )
                )
        | RAbs (x, body) ->
            let res = ref_reduce body in
            ( match res with
            | Some _ -> Some rt
            | _ -> None
            )
        | RVar _ -> None
    in
    let rec loop (rt : ref_lambda ref) : ref_lambda ref =
        let res = ref_reduce rt in
        (* Printf.printf "cur: %s\n" (some |> from_ref_lambda |> string_of_lambda); *)
        match res with
        | None -> rt
        | Some some -> 
            (* Printf.printf "cur: %s\n" (some |> from_ref_lambda |> string_of_lambda); *)
            loop some in
    printf "Renamed term: %s\n" ((string_of_lambda $ (rename_lambda String_map.empty) ) term);
    let ref_term = ref (term |> (rename_lambda String_map.empty) |> to_ref_lambda) in
    ref_term |> loop |> from_ref_lambda
;;