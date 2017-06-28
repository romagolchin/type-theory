module String_map = Map.Make (String);;
type algebraic_term = Var of string | Fun of string * (algebraic_term list)


let str_max s t = 
	if String.length t > String.length s then t else s;;

let new_func_symbol alg_terms =
	let rec longest_id t = 
		match t with
		| Var x -> x 
		| Fun (f, args) -> 
			List.fold_left str_max f (List.rev_map longest_id args) in
	(List.fold_left str_max "" (List.rev_map longest_id alg_terms)) ^ "1" 
	;;

let system_to_equation sys = 
	let (l, r) = List.split sys in
	let f = str_max (new_func_symbol l) (new_func_symbol r) in
	(Fun (f, l), Fun (f, r));; 

let rec apply_substitution subst_list alg_term = 
	let subst_map = List.fold_left (fun map (var, rhs) -> String_map.add var rhs map)
						String_map.empty subst_list in
	let rec helper term = 
		match term with
		| Var x -> if String_map.mem x subst_map then String_map.find x subst_map else Var x
		| Fun (f, args) -> Fun (f, List.map helper args) 
	in helper alg_term;;

let check_solution mb_solution system =
	List.for_all (fun (lhs, rhs) -> 
		(apply_substitution mb_solution lhs) = (apply_substitution mb_solution rhs)) system;;

let rec is_finite x rhs =
	match rhs with
	| Var y -> x <> y
	| Fun (_, args) -> List.for_all (is_finite x) args;;

let rec string_of_alg_term term = 
    match term with
    | Var x -> x
    | Fun (f, args) -> if f = "Impl" 
                            then "(" ^ (string_of_alg_term (List.nth args 0)) ^ ") -> " ^ (string_of_alg_term (List.nth args 1))
                        else let len = List.length args in
                        fst (List.fold_left (fun (s, i) a -> 
                            let str = "(" ^ s ^ (string_of_alg_term a) ^ ")" in
                            if i <> len - 1 
                                then (str ^ " ", i + 1)
                            else (str, i + 1)) ("", 0) args);;


let string_of_sys sys = 
    "{\n" ^ (List.fold_left (fun s (lhs, rhs) -> 
                        s ^ (string_of_alg_term lhs) ^ " = " ^ (string_of_alg_term rhs) ^ "\n"  ) "" sys) ^ "}";;


let rec is_contains (x : string) (t : algebraic_term) : bool =
	match t with
	| Var y -> x = y
	| Fun(_, s) -> List.exists (is_contains x) s;;



let solve_system system =
	let sys_q = ref (Queue.create ()) in
	let push_all l = List.iter (fun eq -> Queue.push eq !sys_q) l in
	push_all system;
	let to_solution ready = 
		(* Printf.printf "Solved\n"; *)
		(* Printf.printf "%s\n" (string_of_sys ready); *)
		List.fold_left (fun res (lhs, rhs) -> match lhs with
										| Var x -> (match res with
											| Some some -> Some ((x, rhs) :: some)
											| _ -> None)
										| _ -> None) (Some []) ready in
	let rec helper ready_number eqs_number = 
		if ready_number = eqs_number 
			then let subst = 
				Queue.fold (fun l x -> x :: l) [] !sys_q in to_solution subst
		else let (lhs, rhs) = Queue.pop !sys_q in
			if lhs = rhs 
				(* delete *)
				then helper 0 (eqs_number - 1)
			else match (lhs, rhs) with
				| (Var x, _) -> 
					if is_finite x rhs 
						(* eliminate *)
						then let sub_q = Queue.create () in
						Queue.fold (fun () (l, r) -> Queue.push (apply_substitution [(x, rhs)] l, apply_substitution [(x, rhs)] r) sub_q) () !sys_q;
						sys_q := sub_q;
						Queue.push (lhs, rhs) !sys_q; 
						helper (ready_number + 1) eqs_number
					(* check *)
					else None
					(* swap *)
				| (Fun (_, _), Var _) -> Queue.push (rhs, lhs) !sys_q; helper 0 eqs_number
				| (Fun (f, args), Fun (f', args')) ->  
					if f <> f' || List.length args <> List.length args' 
						(* conflict *)
						then None
					(* decompose *)
					else let new_eqs = List.combine args args' in
					push_all new_eqs;
					helper 0 (eqs_number + List.length args - 1) in
	helper 0 (List.length system);;
