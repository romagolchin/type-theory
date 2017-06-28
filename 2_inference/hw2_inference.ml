open Hw1_reduction
open Hw2_unify
open Hw1
open Printf 

module String_map = Map.Make (String)

module String_set = Set.Make (String)

type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type
type inference_result = ((string * simp_type) list * simp_type) option
type hm_type = HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type

type hm_lambda = HM_Var of string | HM_Abs of string * hm_lambda | HM_App of hm_lambda * hm_lambda | HM_Let of string * hm_lambda * hm_lambda




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



exception W_exc of string;;
let algorithm_w hml =
    let cnt = ref 0 in
    let get_next_name () = 
        cnt := !cnt + 3;
        "next_type_" ^ (string_of_int !cnt) in
    let get_init_name () = 
        cnt := !cnt + 2;
        "init_type_" ^ (string_of_int !cnt) in

    let rec free_tvars hmt : String_set.t = 
        match hmt with
        | HM_Elem x -> String_set.singleton x
        | HM_ForAll (x, t) -> String_set.remove x (free_tvars t)
        | HM_Arrow (p, q) -> String_set.union (free_tvars p) (free_tvars q)
    in

    let free_tvars_context (cont : hm_type String_map.t) = 
        String_map.fold (fun var hmt ftv -> String_set.union ftv (free_tvars hmt)) cont String_set.empty
    in

    let rec free_vars hml = 
        match hml with
        | HM_Var x -> String_set.singleton x
        | HM_App (p, q) -> String_set.union (free_vars p) (free_vars q)
        | HM_Abs (x, p) -> String_set.remove x (free_vars p)
        (* (\\x.p2) p1 *)
        | HM_Let (x, p1, p2) -> String_set.union (String_set.remove x (free_vars p2)) (free_vars p1)
    in

    (* quantify type using vars from FV(hmt) \ FV(cont) *)
    let closure hmt cont = 
        let tmp = String_set.diff (free_tvars hmt) (free_tvars_context cont) in
        String_set.fold (fun var acc -> HM_ForAll (var, acc)) tmp hmt
    in

    let rec apply_subst (sub : hm_type String_map.t) (hmt : hm_type) : hm_type = 
        match hmt with
        | HM_Elem x ->  if String_map.mem x sub 
                            then (String_map.find x sub)
                        else hmt
        | HM_ForAll (x, t) -> HM_ForAll (x, apply_subst (String_map.remove x sub) t)
        | HM_Arrow (p, q) -> HM_Arrow (apply_subst sub p, apply_subst sub q)

    in

    let rec hmt_to_alg_term hmt =  
        match hmt with
        | HM_Elem x -> Hw2_unify.Var x
        | HM_Arrow (p, q) -> Hw2_unify.Fun ("A", [(hmt_to_alg_term p); (hmt_to_alg_term q) ])
        | _ -> failwith "hmt_to_alg_term : unexpected quantifier"
    in

    let rec alg_term_to_hmt at =  
        match at with
        | Hw2_unify.Var x -> HM_Elem x
        | Hw2_unify.Fun (_, args) -> HM_Arrow ( (alg_term_to_hmt (List.nth args 0)), 
                                                           alg_term_to_hmt (List.nth args 1) )
    in

    let subst_at_to_subst_hmt (s_at : (string * algebraic_term) list) : hm_type String_map.t = 
        List.fold_left (fun acc (var, at) -> String_map.add var (alg_term_to_hmt at) acc) String_map.empty s_at
    in


    let apply_subst_context sub cont = 
        String_map.map (fun hmt -> apply_subst sub hmt) cont
    in


    let ($) sub1 sub2 =  
        let tmp = String_map.map (fun t -> apply_subst sub1 t) sub2 in
        String_map.fold (fun k v map -> if String_map.mem k map 
                                            then map
                                            else String_map.add k v map ) sub1 tmp
    in

    let pair_map f (x, y) = (f x, f y) in

    let rec drop_quantifiers hmt =  
        match hmt with
        | HM_ForAll (x, p) -> drop_quantifiers (apply_subst (String_map.singleton x (HM_Elem (get_next_name ())) ) p)
        | _ -> hmt
    in 


    let rec helper cont (hml : hm_lambda) = 
        match hml with
        | HM_Var x ->
            if String_map.mem x cont then 
                let tx = String_map.find x cont in
                (String_map.empty, drop_quantifiers tx)
            else raise (W_exc (sprintf "var %s is not in context" x))
        | HM_App (e1, e2) -> 
            (
            let (s1, t1) = helper cont e1 in
            let (s2, t2) = helper (apply_subst_context s1 cont) e2 in 
            let t1' = apply_subst s2 t1 in
            let new_tvar = HM_Elem (get_next_name ()) in 
            let t2' = HM_Arrow (t2, new_tvar) in
            let eq = pair_map hmt_to_alg_term (t1', t2')  in  
            match Hw2_unify.solve_system [eq] with
            | Some sol -> 
                let v_sub = subst_at_to_subst_hmt sol in
                let comp = v_sub $ s2 $ s1 in 
                (comp, apply_subst comp new_tvar)
            | _ -> raise (W_exc "unification failed")
            )
        | HM_Abs (x, e1) -> 
            let new_tvar = HM_Elem (get_next_name ()) in
            let cont' = String_map.add x new_tvar cont in 
            let s1, t1 = helper cont' e1 in
            (s1, HM_Arrow (apply_subst s1 new_tvar, t1))
        | HM_Let (x, e1, e2) ->
            let s1, t1 = helper cont e1 in
            let s1_cont = apply_subst_context s1 cont in
            let s1_cont_x = apply_subst_context s1 (String_map.remove x cont) in
            let cl = closure t1 s1_cont in
            let s2, t2 = helper (String_map.add x cl s1_cont_x) e2 in
            (s2 $ s1, t2)
    in

    let fv = free_vars hml in
    let init_cont = String_set.fold (fun x map -> String_map.add x (HM_Elem (get_init_name ())) map) fv String_map.empty in 

    try
        let (sub, tp) = helper init_cont hml in Some (String_map.bindings sub, tp)
    with
    | _ -> None



;;
