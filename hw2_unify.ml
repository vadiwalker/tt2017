open List;;
type algebraic_term = Var of string | Fun of string * (algebraic_term list)

let x = ref 0;;
let rec new_var c = x := !x + 1; ("n" ^ string_of_int(!x))
;;

let system_to_equation x = (Fun((new_var ()), (map fst x)), Fun((new_var ()), (map snd x)))
;;

let rec take s x = match s with
	| [] -> Var(x)
	| e :: ss -> if (fst e) = x then (snd e) else (take ss x)
;;

let rec apply_substitution s x = match x with
	| Var(a) -> (take s a)
	| Fun(f, xs) -> Fun(f, (map (apply_substitution s) xs))
;; 

let rec equals_to_all x y = match x, y with
	| [], [] -> true
	| Var(a) :: xs, Var(b) :: ys -> if a = b then equals_to_all xs ys else false
	| Fun(f, fs) :: xs, Fun(g, gs) :: ys -> if f = g then (equals_to_all fs gs) && (equals_to_all xs ys) else false
	| _, _ -> false
;; 

let equals_to x y = equals_to_all [x] [y]
;;

let check_solution s x = let y = (system_to_equation x) in
							equals_to (apply_substitution s (fst y)) (apply_substitution s (snd y))
;;

let rec come_in x a = match a with
	| Var(y) -> if x = y then true else false
	| Fun(f, ys) -> if (filter (come_in x) ys) = [] then false else true
;;

let is_incompatible_single x = match x with
	| Fun(f, xs), Fun(g, ys) -> if f = g then false else true
	| Var(a), Fun(f, ys) -> (come_in a (Fun(f, ys)))
	| _, _ -> false
;;

let rec is_incompatible x = if (filter is_incompatible_single x) = [] then false else true
;;

let rec matches_single_term a term = match term with
	| Var(b) -> if a = b then 1 else 0
	| Fun(f, terms) -> fold_left (+) 0 (map (matches_single_term a) terms)
;;

let rec matches_single a terms = match terms with
	| x, y -> (matches_single_term a x) + (matches_single_term a y)
;;

let matches all a = fold_left (+) 0 (map (matches_single a) all)
;;

let is_solved_single all x = match x with
	| Var(a), _ -> if (matches all a) = 1 then true else false
	| _, _ -> false

let is_solved x = fold_left (&&) true (map (is_solved_single x) x)
;;

let rec remove a_to_remove x = match x with
	| [] -> []
	| first :: xs -> if first = a_to_remove then (remove a_to_remove xs) else [first] @ (remove a_to_remove xs)
;;

let is_ready_to_replace_single all x = match x with
	| Var(a), Var(b) -> if a = b then true else false
	| Fun(f, fs), Var(a) -> true
	| Fun(f, fs), Fun(g, gs) -> if f = g then true else false
	| Var(a), Fun(f, fs) -> if (matches all a) > 1 then true else false
;;

let is_ready_to_replace x = fold_left (&&) true (map (is_ready_to_replace_single x) x)
;;

let rec reduce_f fs gs = match fs, gs with
	| [], [] -> []
	| x :: fs_rem, y :: gs_rem -> [(x, y)] @ (reduce_f fs_rem gs_rem)
	| _, _ -> []
;;

let rec apply_substitution_to_all s x = match x with
	| [] -> []
	| (a, b) :: tail -> ((apply_substitution s a), (apply_substitution s b)) :: (apply_substitution_to_all s tail)
;;

let rec var_equals_to a b = match a, b with
	| Var(x), Var(y) -> if x = y then true else false
	| _, _ -> false
;; 

let rec try_replace all x = match x with
	| Fun(f, fs), Var(a) as cur -> Some([(Var(a), Fun(f, fs))] @ (remove cur all))
	| Fun(f, fs), Fun(g, gs) as cur -> if f = g then Some( (remove cur all) @ (reduce_f fs gs) ) else None
	| Var(a), b as cur -> if (var_equals_to (Var(a)) b) then Some((remove cur all)) else
							if (matches all a) > 1 then Some( (apply_substitution_to_all [a, b] (remove cur all)) @ [(Var(a), b)] )
													else None
;;

let rec unpack x = match x with
	| Some y -> y
	| None -> raise (Invalid_argument "Option.get")
;;

let rec replace all x = match x with
	| [] -> all
	| head :: tail -> let nw_all = try_replace all head in
						if nw_all = None then replace all tail
							else unpack nw_all
;;

let rec system_to_sub x = match x with
	| [] -> []
	| (Var(x), a) :: tail -> (x, a) :: (system_to_sub tail)
	| _ -> raise (Invalid_argument "System_to_sub")
;;

(* --------------------- PRINTS ----------------------- *)

let rec print_terms a = match a with
	| [] -> print_string ""
	| head :: tail -> match head with 
		| Var(x) -> print_string x ; print_string ", " ; print_terms tail
		| Fun(f, fs) -> print_string (f ^ "("); print_terms fs ; print_string "), " ; print_terms tail
;;

let rec print_term x = print_terms [x]
;;

let rec print_eq eq = match eq with
	| [] -> ()
	| (x, y) :: tail -> print_term x ; print_string " = " ; print_term y ; print_string "\n" ; print_eq tail
;;

let rec print_sub x = match x with
	| [] -> ()
	| head :: tail -> print_string ((fst head) ^ " = "); print_term (snd head) ; print_string "\n" ; print_sub tail  
;;

(* --------------------- END PRINTS ----------------------- *)

let rec solve_system x = if is_solved x then Some (system_to_sub x) else 
						if is_incompatible x then None
							else (* let expr = print_string "-----\n" ; print_eq x ; print_string "-----\n" in  *)solve_system (replace x x) 
;;

(* let eq1 = (Fun("g", [Var("x2")]), Var("x1"));;
let eq2 = (Fun("f", [ Var("x1") ; Fun("h", [Var("x1")]); Var("x2") ]), Fun("f", [Fun("g", [Var("x3")]) ; Var("x4"); Var("x3")]));;

let eq = [ eq1 ; eq2 ];;

if (solve_system eq) = None then print_string "No decisions" else print_sub (unpack (solve_system eq))
;; *)