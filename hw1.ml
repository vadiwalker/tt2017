open Char;;
open String;;
open List;;
type peano = Z | S of peano;;
type lambda = Var of string | Abs of string * lambda | App of lambda * lambda;;

let rec peano_of_int x = if x = 0 then Z else S (peano_of_int (x - 1))

let rec int_of_peano x = match x with 
	S suff -> int_of_peano suff + 1
	| Z -> 0;;

let inc x = S x;;

let rec add x y = match y with 
	Z -> x
	| S y -> S (add x y);;

let rec mul x y = match y with
	Z -> Z
	| S y -> add (mul x y) x;;

let rec power x y = match y with 
	Z -> S Z
	| S y -> mul (power x y) x;;


let rec cmp x y = match x, y with 
	Z, Z -> 0
	| _, Z -> 1
	| Z, _ -> -1
	| (S x, S y) -> cmp x y;;

let rec sub x y = match x, y with 
	_, Z -> x
	| S x, S y -> sub x y
	| _ -> failwith("(sub small big) exception");;

let rec div x y = if cmp x y = -1 then Z else S (div (sub x y) y);;

let rec peano_string x = match x with
	Z -> "Z"
	| S x -> "S(" ^ peano_string x ^ ")";;


(* reverse module*)

let rec revhelper revhead tail = match tail with
	[] -> revhead
	| element :: tail -> revhelper (element :: revhead) tail;;

let rev x = revhelper [] x;;

(*merge sort*)
let rec halve lst = match lst with 
	[] -> [], []
	| a :: [] as t -> t, []
	| a :: (b :: lst) -> let lst1, lst2 = halve lst in
								a :: lst1, b :: lst2
;;

 let rec merge = function
	| a, [] -> a
	| [], b -> b
	| a :: at, b :: bt ->
	if a <= b then a :: (merge(at, b :: bt))
				else b :: (merge(a :: at, bt))
;;

let rec merge_sort = function 
	| [] as ret -> ret
	| _ :: [] as ret -> ret
	| lst -> let (part1, part2) = halve lst in
		merge(merge_sort part1, merge_sort part2)
;;

let rec print_list = function
	| [] -> print_string "\n"
	| element :: tail ->
	 print_int element; print_string " "; (print_list tail)
;;



(* print_list (merge_sort (Cons (89, Cons(100, Cons(10, Cons(156, Cons(-456, Nil)))))));;
 *)

let lambda_of_string expr = 
	let pos = ref 0 in

	let next () = (pos := !pos + 1) in 

	let rec cchar () = if !pos >= (String.length expr) then '!' else 
													let cur = (String.get expr !pos) in
														if cur = ' ' then (next(); cchar()) else cur in 

	let cchar_without_moving () = if !pos >= (String.length expr) then '!' else (String.get expr !pos) in


	let is_letter x = (('a' <= x) && (x <= 'z')) in

	let is_big_letter x = (('A' <= x) && (x <= 'Z')) in

	let is_digit x = (('0' <= x) && (x <= '9')) in

	let rec tail_var () =
		let x = cchar_without_moving () in
			if (is_letter x) || (is_digit x) || (is_big_letter x) then (Char.escaped x) ^ (next(); tail_var()) else "" in

	let rec var () =
		let x = cchar_without_moving () in
		if is_letter x then (Char.escaped x) ^ (next (); tail_var ()) else "" in
	
	let rec app_of a = match a with
		| x :: y :: tail -> (app_of ((App(x, y)) :: tail))
		| x :: [] -> x
		| [] -> raise (Invalid_argument "App of") in

	let rec push a x = match a with
		| [] -> [x]
		| head :: tail -> head :: (push tail x) in

	let rec lambda x =
		if ((is_letter (cchar ()) = false) && (cchar() != '(') && (cchar() != '\\')) then
								(app_of x) else match cchar() with
		| ' ' -> next(); (lambda x)

		| '\\' ->
		  let a = next(); var() in
		  	let b = (assert (cchar() = '.')); next(); (lambda []) in
		 	 (lambda (push x (Abs(a, b)))) 

		| '(' -> let ret = next (); (lambda []) in 
				(assert (cchar() = ')')); next (); (lambda (push x ret))

		| y -> if is_letter y then (lambda (push x (Var(var()))))
								else failwith "Invalid expression!" in

	lambda [];;

let rec string_of_lambda = function 
	| Var x -> x
	| Abs (x, y) -> "(" ^ "\\" ^ x ^ "." ^ (string_of_lambda y) ^ ")"
	| App (x, y) -> "(" ^ (string_of_lambda x) ^ (string_of_lambda y) ^ ")";;


(* print_string (string_of_lambda s);; *)

(* let var = 10;;
print_int var;; *)


(* 
print_string (string_of_lambda (Abs("x", Var("x"))));;
print_string "\n";;
print_string (string_of_lambda (Var "x"));; 
 

print_string (string_of_lambda (lambda_of_string "\\x.(\\y.(a(b)))"));;


 print_string "\n";;*)