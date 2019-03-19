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
	| Abs(x, a), Abs(y, b) -> let n = new_var () in
								(is_alpha_equivalent (sub a x (Var (n))) (sub b y (Var (n))))
	| _, _ -> false
;;

let rec rename a map = match a with
	| Abs(x, b) -> let nv = new_var () in
					(Hashtbl.add map x nv) ; Abs(nv, rename b map)

	| App(x, y) -> App(rename x map, rename y map)

	| Var(x) -> if (Hashtbl.mem map x) then Var(Hashtbl.find map x) else Var(x)
;;

let rec rename_to_format a map = match a with
	| Var(x) -> if (Hashtbl.mem map x) then Var(Hashtbl.find map x) else Var(x)
	| Abs(x, b) -> let nx = "abs" ^ (string_of_int (Hashtbl.length map)) in
					(Hashtbl.add map x nx) ; Abs(nx, rename_to_format b map)
	| App(x, y) -> App(rename_to_format x map, rename_to_format y map)
;;

module H = Hashtbl.Make(struct
  type t = lambda
  let equal = is_alpha_equivalent
  let hash a = Hashtbl.hash (rename_to_format a (Hashtbl.create 10))
end);;

let rec normal_beta_reduction p = match p with
	| Var x -> Var x
	| App(Abs(x, a), b) ->	let magic_hashtbl = (Hashtbl.create 10) in
								let re_a = (Hashtbl.add magic_hashtbl x x) ; rename a magic_hashtbl in
									  sub re_a x b

	| App(a, b) -> if not (is_normal_form a) then App(normal_beta_reduction a, b) 
		else App(a, normal_beta_reduction b)
	| Abs(x, a) -> Abs(x, normal_beta_reduction a)

(* let rec reduce_to_normal_form p = if is_normal_form p then p else reduce_to_normal_form (normal_beta_reduction p)
;; *)

(* let map = ref [];;

let rec push_to_map e = map := e :: !map ; ();;

let rec reduce_to_normal_form p = if is_normal_form p then p else 
									if (mem_assoc p !map) then (assoc p !map) else
										let x = (reduce_to_normal_form (normal_beta_reduction p)) in
											push_to_map (p, x) ;
												x
;; *)
										

let rec mem_reduce_to_normal_form p reduced = if (H.mem reduced p) then (print_string "FIND"; (H.find reduced p, reduced)) else match p with
	| Var x -> (Var x, reduced)
	
	| App(Abs(x, a), b) -> let (p1, reduced1) = mem_reduce_to_normal_form a reduced in
							let (p2, reduced2) = mem_reduce_to_normal_form b reduced1 in
								let magic_hashtbl = (Hashtbl.create 10) in
									let re_p1 = (Hashtbl.add magic_hashtbl x x) ; rename p1 magic_hashtbl in
										let expr = (sub re_p1 x p2) in
											(H.add reduced2 p expr) ; (expr, reduced2)

	| App(a, b) -> let (p1, reduced1) = mem_reduce_to_normal_form a reduced in
					let (p2, reduced2) = mem_reduce_to_normal_form b reduced1 in
						let expr = App(p1, p2) in
							(H.add reduced2 p expr) ; (expr, reduced2)

	| Abs(x, a) -> let (p1, reduced1) = mem_reduce_to_normal_form a reduced in
					let expr = Abs(x, p1) in
						(H.add reduced1 p expr) ; (expr, reduced1)
;;



let rec reduce_to_normal_form_recurisve p map = if is_normal_form p then p else
													let (p1, map1) = (mem_reduce_to_normal_form p map) in
															reduce_to_normal_form_recurisve p1 map1
;;

let rec reduce_to_normal_form p = reduce_to_normal_form_recurisve p (H.create 10)
;;

let s = lambda_of_string("(   \\f.(\\x.   (f00123 fasds21312S f f f f f f x   ))  f )");;

(* print_string (string_of_lambda s);; *)

let add = lambda_of_string "((\\a.\\b.\\f.\\x. a f (b f x)) (\\f.\\x. f (f (f (f (f(x))))))) (\\f.\\x. (f(f(f(x)))))"
;;

let dir = lambda_of_string "a b c"
;;

let lmd1 = lambda_of_string "((\\x.\\y.x) (\\z.y)) k";;
(* print_string (string_of_lambda (normal_beta_reduction lmd1));; print_newline ();;(*  *)
print_string (string_of_lambda (reduce_to_normal_form lmd1));; print_newline ();; *)


let h = (H.create 10);;
(H.add h (Var("x")) "x");;
(H.add h (Abs("x", Var("x"))) "expression");;
(* print_string (string_of_bool (H.mem h (Abs("y", Var("y")))));; *)

(* print_string (string_of_bool (is_alpha_equivalent (Abs("x", Var("x"))) (Abs("y", Var("x")))));; *)

(* let lmd1 = lambda_of_string "\\x.x";;
let lmd2 = lambda_of_string "\\y.y";;

print_string (if is_alpha_equivalent (lmd1) (lmd2) then "true" else "false");; *)

(* print_string(string_of_lambda(dir));; *)
print_string(string_of_lambda(reduce_to_normal_form add));;
(* print_string (string_of_int (length !map));; *)

(* print_string (string_of_lambda (reduce_to_normal_form s));; *)

(* print_string (string_of_lambda (reduce_to_normal_form (App(Abs("x", Var "x"), Var "y"))));; *)