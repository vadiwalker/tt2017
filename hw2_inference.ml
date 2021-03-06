open Hw1;;
open Hw2_unify;;
open Hw1_reduction;;

type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type
type hm_lambda = HM_Var of string | HM_Abs of string * hm_lambda | HM_App of hm_lambda * hm_lambda | HM_Let of string * hm_lambda * hm_lambda
type hm_type = HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type

let y = S_Elem "X";;

(* print_int(!x);; *)

let x = ref 0;;
let rec new_var c = x := !x + 1; ("n" ^ string_of_int(!x))
;;

let rec infer_simp_equations a = match a with
	| Hw1.Var x -> ([], S_Elem(x))
	| App(p, q) -> let (pE, pT) = (infer_simp_equations p) in
					let (qE, qT) = (infer_simp_equations q) in
						let aT = S_Elem(new_var ()) in
							(pE @ qE @ [pT, S_Arrow(qT, aT)], aT)
	| Abs(x, p) -> let (pE, pT) = (infer_simp_equations p) in
					(pE, S_Arrow(S_Elem(x), pT))
;;

let rec simp_expr_to_alg a = match a with
	| S_Elem(x) -> Hw2_unify.Var(x)
	| S_Arrow(x, y) -> Hw2_unify.Fun("f", [(simp_expr_to_alg x) ; (simp_expr_to_alg y)])
;;

let rec simp_eq_to_alg a = match a with
	| [] -> []
	| (x, y) :: tail -> ((simp_expr_to_alg x), (simp_expr_to_alg y)) :: (simp_eq_to_alg tail)
;;

let rec alg_expr_to_simp a = match a with
	| Hw2_unify.Var(x) -> S_Elem(x)
	| Hw2_unify.Fun(f, [x; y]) -> S_Arrow((alg_expr_to_simp x), (alg_expr_to_simp y))
	| _ -> S_Elem("undefined_algebraic")
;;

let rec alg_eq_to_simp a = match a with
	| [] -> []
	| (x, y) :: tail -> ((alg_expr_to_simp x), (alg_expr_to_simp y)) :: (alg_eq_to_simp tail)
;;

let rec unpack x = match x with
	| Some y -> y
	| None -> raise (Not_found)
;;

let rec apply_substitution_to_var s v = match s with
	| [] -> S_Elem(v)
	| (x, y) :: tail -> if x = v then (alg_expr_to_simp y) else (apply_substitution_to_var tail v)
;; 

let rec apply_substitution_to_vars s v = match v with
	| [] -> []
	| head :: tail -> (apply_substitution_to_var s head) :: (apply_substitution_to_vars s tail)
;;

let rec connect a b = match a, b with
	| [], [] -> []
	| x :: a_tail, y :: b_tail -> (x, y) :: (connect a_tail b_tail)
	| _, _ -> raise (Invalid_argument "Connect")
;;

let rec infer_simp_type a = let (eqs, t) = infer_simp_equations a in
								let (alg_eqs, alg_type) = (simp_eq_to_alg eqs), (simp_expr_to_alg t) in
									let alg_sub = (solve_system alg_eqs) in
										if alg_sub = None then None else
											let free_vs = free_vars a in 
												let g = (apply_substitution_to_vars (unpack alg_sub) free_vs) in
													Some ((connect free_vs g), (alg_expr_to_simp (apply_substitution (unpack alg_sub) alg_type)))
;;

let expr = Abs("f", Abs("x", App(Var("f"), App(Var("f"), Var("x")))));;
let solution = infer_simp_type expr;;

let rec string_of_simp_type t = match t with
	| S_Elem x -> x
	| S_Arrow(a, b) -> (string_of_simp_type a) ^ "->" ^ (string_of_simp_type b)
;;

(* if (solution = None) then print_string "No solution" else 
	print_string (string_of_simp_type (snd (unpack solution)));;
 *)
let rec rename a = failwith "Not implemented";;

let rec get_from_G g m = match g with
	| [] -> None
	| (x, y) :: tail -> if x = m then Some y else get_from_G tail m
;;

let rec sub a var to_s = match a with
	| HM_ForAll(x, y) -> HM_ForAll(x, sub y var to_s)
	| HM_Elem(x) as cur -> if x = var then to_s else cur
	| HM_Arrow(x, y) -> HM_Arrow(sub x var to_s, sub y var to_s)
;;

let rec remove_quantifiers t = match t with
	| HM_ForAll(x, y) -> remove_quantifiers (sub y x (HM_Elem(new_var ())))
	| _ as cur -> cur
;;

let rec exists_s a x = match a with
	| [] -> false
	| head :: tail -> if head = x then true else (exists_s tail x)
;;

let rec merge_s a b = match a with 
	| [] -> b
	| head :: tail -> if exists_s b head then merge_s tail b else merge_s tail (head :: b)
;;

let rec remove_s a x = match a with 
	| [] -> []
	| head :: tail -> if head = x then (remove_s tail x) else head :: (remove_s tail x)
;;

let rec exclude_s a b = match b with
	| [] -> a
	| head :: tail -> (exclude_s (remove_s a head) tail)
;;

let rec hm_free_vars a = match a with
	| HM_Elem(x) -> [x]
	| HM_Arrow(x, y) -> merge_s (hm_free_vars x) (hm_free_vars y)
	| HM_ForAll(x, y) -> remove_s (hm_free_vars y) x
;;

let rec add_quantifiers_s t qs = match qs with 
	| [] -> t
	| head :: tail -> HM_ForAll(head, (add_quantifiers_s t tail))
;;

let rec hm_G_free_vars g = match g with
	| [] -> []
	| (x, y) :: tail -> merge_s (hm_free_vars y) (hm_G_free_vars tail)
;;

let rec add_quantifiers g t = add_quantifiers_s t (hm_free_vars t)
;;

let rec apply_var_sub s var = match s with
	| [] -> HM_Elem(var)
	| (x, y) :: tail -> if x = var then y else (apply_var_sub tail var)
;;

let rec apply_single_sub s term = match term with
	| HM_Elem(x) -> apply_var_sub s x
	| HM_Arrow(x, y) -> HM_Arrow(apply_single_sub s x, apply_single_sub s y)
	| HM_ForAll(x, y) -> HM_ForAll(x, apply_single_sub s y)
;;

let rec add_required_id v it_g = match it_g with
	| [] -> [(v, HM_Elem(v))]
	| (x, y) :: tail -> if x = v then it_g else ((x, y) :: (add_required_id v tail))
;;

let rec add_required_ids it_f g = match it_f with
	| [] -> g
	| (x, y) :: tail -> (add_required_ids tail (add_required_id x g))

let rec composition f g = match g with
	| [] -> []
	| (x, y) :: tail -> (x, (apply_single_sub f y))	:: (composition f tail)
;;

let rec smart_composition f g = composition f (add_required_ids f g)
;; 

let rec remove_x g x = match g with
	| [] -> []
	| (a, b) :: tail -> if a = x then (remove_x tail x) else (a, b) :: (remove_x tail x)
;;

let rec apply_substitution_to_g s g = match g with
	| [] -> []
	| (x, t) :: tail -> (x, apply_single_sub s t) :: (apply_substitution_to_g s tail)
;;

let rec unpack_var x = match x with
	| Hw2_unify.Var(y) -> y
	| _ -> raise (Invalid_argument "unpack_var")
;;

let rec hm_type_of_alg a = match a with
	| Hw2_unify.Var(x) -> HM_Elem(x)
	| Hw2_unify.Fun(f, [x; y]) -> HM_Arrow(hm_type_of_alg x, hm_type_of_alg y)
	| _ -> raise (Invalid_argument "hm_type_of_alg")
;;

let rec alg_of_hm_type a = match a with
	| HM_Elem(x) -> Hw2_unify.Var(x)
	| HM_Arrow(x, y) -> Hw2_unify.Fun("f", [alg_of_hm_type x; alg_of_hm_type y])
	| HM_ForAll(x, y) as cur -> alg_of_hm_type (remove_quantifiers cur)
;;

let rec hm_type_sub_of_alg_sub s = match s with
	| [] -> []
	| head :: tail -> match head with
		| (x, y) -> (x, hm_type_of_alg y) :: (hm_type_sub_of_alg_sub tail)
;;

let rec string_of_hm_type a = match a with
	| HM_Elem(x) -> x
	| HM_Arrow(x, y) -> (string_of_hm_type x) ^ " -> " ^ (string_of_hm_type y)
	| HM_ForAll(x, y) -> "V(" ^ x ^ ")." ^ (string_of_hm_type y)
;;

let rec sup_algorithm_w g m = match m with 
	| HM_Var(a) -> let t = get_from_G g m in
						if t = None then None
							else Some ([], (remove_quantifiers (unpack t)))

	| HM_App(e1, e2) -> let ret = (try let (s1, t1) = unpack (sup_algorithm_w g e1) in
								let (s2, t2) = unpack (sup_algorithm_w (apply_substitution_to_g s1 g) e2) in
									let beta = HM_Elem(new_var ()) in
										let alg_v = solve_system [alg_of_hm_type (apply_single_sub s2 t1), alg_of_hm_type (HM_Arrow(t2, beta))] in
											if alg_v = None then None else let v = hm_type_sub_of_alg_sub (unpack alg_v) in
												let s = smart_composition (smart_composition v s1) s2 in
													Some (s, (apply_single_sub s beta))
									with Not_found -> None) in ret

	| HM_Abs(x, e) -> let ret = (try let beta = HM_Elem(new_var ()) in
						let (s1, t1) = unpack (sup_algorithm_w ([(HM_Var(x), beta)] @ (remove_x g (HM_Var(x)))) e) in
								Some (s1, HM_Arrow(apply_single_sub s1 beta, t1))
					  			with Not_found -> None) in ret

	(* | HM_Let(x, e1, e2) -> let sol1 = sup_algorithm_w g e1 in
								if sol1 = None then None else let (s1, t1) = unpack sol1 in
									let sol2 = sup_algorithm_w (apply_substitution_to_g s1 ((remove_x g (HM_Var(x))) @ [(HM_Var(x), add_quantifiers t1)])) e2 in
										if sol2 = None then None else let (s2, t2) = unpack sol2 in
											Some ((smart_composition s2 s1), t2) *)

										
	| HM_Let(x, e1, e2) -> let ret = (try let (s1, t1) = unpack (sup_algorithm_w g e1) in
								let s1g = apply_substitution_to_g s1 g in
									let x_type = (add_quantifiers s1g t1) in
										let s1g_with_x = (remove_x s1g (HM_Var(x))) @ [HM_Var(x), x_type] in
											let (s2, t2) = unpack (sup_algorithm_w s1g_with_x e2) in
												Some ((smart_composition s2 s1), t2)
										with Not_found -> None) in ret
;;

let rec algorithm_w a = sup_algorithm_w [] a
;;

let rec string_of_sub a = match a with
	| [] -> ""
	| (x, y) :: tail -> x ^ " = " ^ (string_of_hm_type y) ^ "\n" ^ (string_of_sub tail) 
;;

(* let x = HM_Abs("f", HM_Abs("x", HM_App(HM_Var("f"), HM_App(HM_Var("f"), HM_App(HM_Var("f"), HM_Var("x"))))))
;;

let hm_one = HM_Abs("f", HM_Abs("x", HM_App(HM_Var("f"), HM_Var("x"))))
;;

let expr = HM_Let("sg", hm_one, HM_App(HM_Var("sg"), HM_Var("sg")));;
 *)
(* 
let v = [("x", HM_Elem("n1")); ("n1", HM_Elem("n2"))];;
let s = [("f", HM_Arrow(HM_Elem("x"), HM_Elem("n1")))];; *)

(* print_string (string_of_sub (smart_composition v s));; *)

(* if algorithm_w expr = None then print_string ("No Decision!!!") else 
		let (s, t) = (unpack (algorithm_w x)) in
			print_string (string_of_hm_type t) (* ; print_string (string_of_sub s) *)
;; *)