open List;;
open Hw1;;

let x = ref 0;;
let rec new_var c = x := !x + 1; ("n" ^ string_of_int(!x))
;;

let rec drop_element a to_drop = match a with
	| [] -> []
	| head :: tail -> 
		if head = to_drop then drop_element tail to_drop 
		else head :: (drop_element tail to_drop)
;;

let rec merge a b = match a with
	| [] -> b
	| head :: tail -> merge tail (head :: b)
;;

let rec free_vars expr = match expr with
	| Var x -> x :: []
	| Abs(x, p) -> drop_element (free_vars p) x
	| App(p, q) -> merge (free_vars p) (free_vars q)
;;

let rec in_list a to_check = match a with
	| [] -> false
	| x :: tail -> if x = to_check then true else in_list tail to_check
;;

let rec is_intersection a b = match a with 
	| [] -> false
	| x :: tail -> if (in_list b x) then true else is_intersection tail b
;;


let rec free_to_subst_c q p x abss = match p with
	| Var y -> if x = y then not (is_intersection (free_vars q) abss) else true
	| Abs(y, a) -> free_to_subst_c q a x (y :: abss)
	| App(a, b) -> (free_to_subst_c q a x abss) && (free_to_subst_c q a x abss)

(* p[x = q] *)
let rec free_to_subst q p x = free_to_subst_c q p x [];;

let rec is_normal_form p = match p with
	| Var(_) -> true
	| App(Abs(_, _), _) -> false
	| App(a, b) -> (is_normal_form a) && (is_normal_form b)
	| Abs(x, b) -> (is_normal_form b)
;;

(* p[x = q] *)
let rec sub p x q = match p with
	| Var(y) as arg -> if x = y then q else arg
	| Abs(y, a) -> Abs(y, sub a x q)
	| App(a, b) -> App((sub a x q), (sub b x q));
;;

let rec is_alpha_equivalent p q = match p, q with
	| Var x, Var y -> if x = y then true else false
	| App(a, b), App(c, d) -> (is_alpha_equivalent a c) && (is_alpha_equivalent b d)
	| Abs(x, a), Abs(y, b) -> (is_alpha_equivalent (sub a x (Var (new_var ()))) (sub b y (Var (new_var ()))))
	| _, _ -> false
;;

let rec normal_beta_reduction p = match p with
	| Var x -> Var x
	| App(Abs(x, a), b) -> sub a x b
	| App(a, b) -> if not (is_normal_form a) then App(normal_beta_reduction a, b) 
		else App(a, normal_beta_reduction b)
	| Abs(x, a) -> Abs(x, normal_beta_reduction a)

(* let rec reduce_to_normal_form p = if is_normal_form p then p else reduce_to_normal_form (normal_beta_reduction p)
;; *)

let map = ref [];;

let rec push_to_map e = map := e :: !map ; ();;

let rec reduce_to_normal_form p = if is_normal_form p then p else 
									if (mem_assoc p !map) then (assoc p !map) else
										let x = (reduce_to_normal_form (normal_beta_reduction p)) in
											push_to_map (p, x) ;
												x
;;
										

(* let rec mem_reduce_to_normal_form p reduced = if (mem_assoc p reduced) then (assoc p reduced, reduced) else match p with
	| Var x -> (Var x, reduced)
	| App(Abs(x, a), b) -> let (p1, reduced1) = mem_reduce_to_normal_form a reduced in
							let (p2, reduced2) = mem_reduce_to_normal_form b reduced1 in
								let expr = (sub p1 x p2) in
									(expr, (p, expr) :: reduced2)

	| App(a, b) -> let (p1, reduced1) = mem_reduce_to_normal_form a reduced in
					let (p2, reduced2) = mem_reduce_to_normal_form b reduced1 in
						let expr = App(p1, p2) in
							(expr, (p, expr) :: reduced2)

	| Abs(x, a) -> let (p1, reduced1) = mem_reduce_to_normal_form a reduced in
					let expr = Abs(x, p1) in
						(expr, (p, expr) :: reduced1)
;;

let rec reduce_to_normal_form_recurisve p map = if is_normal_form p then p else
													let (p1, map1) = (mem_reduce_to_normal_form p map) in
														let w = print_string ((string_of_int (length map1)) ^ "\n") in
															reduce_to_normal_form_recurisve p1 map1
;; *)

(* let rec reduce_to_normal_form p = reduce_to_normal_form_recurisve p []
;;
 *)
let s = lambda_of_string("(   \\f.(\\x.   (f00123 fasds21312S f f f f f f x   ))  f )");;

(* print_string (string_of_lambda s);; *)

let add = lambda_of_string "((\\a.\\b.\\f.\\x. a f (b f x)) (\\f.\\x. f (f (f (f (f(x))))))) (\\f.\\x. (f(f(f(x)))))"
;;

let dir = lambda_of_string "a b c"
;;

(* print_string(string_of_lambda(dir));; *)
(* print_string(string_of_lambda(reduce_to_normal_form add));;
print_string (string_of_int (length !map));;
 *)
(* print_string (string_of_lambda (reduce_to_normal_form s));; *)

(* print_string (string_of_lambda (reduce_to_normal_form (App(Abs("x", Var "x"), Var "y"))));; *)