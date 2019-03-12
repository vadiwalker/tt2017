open List;;
open Hw1

let rec drop_element a to_drop = match a with
	| Nil -> Nil
	| Cons(head, tail) -> 
		if head = to_drop then drop_element tail to_drop 
		else Cons(head, (drop_element tail to_drop))
;;

let rec merge a b = match a with
	| Nil -> b
	| Cons(head, tail) -> merge tail (Cons(head, b))
;;

let rec free_vars expr = match expr with
	| Var x -> Cons(x, Nil)
	| Abs(x, p) -> drop_element (free_vars p) x
	| App(p, q) -> merge (free_vars p) (free_vars q)
;;

let rec in_list a to_check = match a with
	| Nil -> false
	| Cons(x, tail) -> if x = to_check then true else in_list tail to_check
;;

let rec is_intersection a b = match a with 
	| Nil -> false
	| Cons(x, tail) -> if (in_list b x) then true else is_intersection tail b
;;


let rec free_to_subst_c q p x abss = match p with
	| Var y -> if x = y then not (is_intersection (free_vars q) abss) else true
	| Abs(y, a) -> free_to_subst_c q a x (Cons(y, abss))
	| App(a, b) -> (free_to_subst_c q a x abss) && (free_to_subst_c q a x abss)

(* p[x = q] *)
let rec free_to_subst q p x = free_to_subst_c q p x Nil;;

let rec is_normal_form p = match p with
	| Var _ -> true
	| App(Abs(_, _), _) -> false
	| App(a, b) -> (is_normal_form a) && (is_normal_form b)
	| Abs(x, b) -> (is_normal_form b)
;;

(* p[x = q] *)
let rec sub p x q = match p with
	| Var y as arg -> if x = y then q else arg
	| Abs(y, a) -> Abs(y, sub a x q)
	| App(a, b) -> App((sub a x q), (sub b x q));
;;

let rec is_alpha_equivalent p q = match p, q with
	| Var x, Var y -> if x = y then true else false
	| App(a, b), App(c, d) -> (is_alpha_equivalent a c) && (is_alpha_equivalent b d)
	| Abs(x, a), Abs(y, b) -> (is_alpha_equivalent (sub a x (Var "t")) (sub b y (Var "t")))
	| _, _ -> false
;;

let rec normal_beta_reduction p = match p with
	| Var x -> Var x
	| App(Abs(x, a), b) -> sub a x b
	| App(a, b) -> if not (is_normal_form a) then App(normal_beta_reduction a, b) 
		else App(a, normal_beta_reduction b)
	| Abs(x, a) -> Abs(x, normal_beta_reduction a)

let rec reduce_to_normal_form p = if is_normal_form p then p else reduce_to_normal_form (normal_beta_reduction p)
;;

let rec mem_reduce_to_normal_form p reduced = if (mem_assoc p reduced) then (assoc p reduced, reduced) else match p with
	| Var x -> (Var x, reduced)
	| App(Abs(x, a), b) -> let c = mem_reduce_to_normal_form a reduced in
							let d = mem_reduce_to_normal_form b (snd c) in
								let expr = (sub (fst c) x (fst d)) in
									(expr, (p, expr) :: (snd d))
	| App(a, b) -> let c = mem_reduce_to_normal_form a reduced in
					let d = mem_reduce_to_normal_form b (snd c) in
						let expr = App((fst c), (fst d)) in
							(expr, (p, expr) :: (snd d))
	| Abs(x, a) -> let c = mem_reduce_to_normal_form a reduced in
					let expr = Abs(x, (fst c)) in
						(expr, (p, expr) :: (snd c))
;;

let rec reduce_to_normal_form p = (fst (mem_reduce_to_normal_form p [(Var "x", Var "x")]))
;;

(* print_string (string_of_lambda (reduce_to_normal_form (App(Abs("x", Var "x"), Var "y"))));; *)