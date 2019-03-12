open Char;;
open String;;
type peano = Z | S of peano;;
type lambda = Var of string | Abs of string * lambda | App of lambda * lambda;;
type 'a list = Nil | Cons of 'a * 'a list;;

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
	Nil -> revhead
	| Cons (element, tail) -> revhelper (Cons (element, revhead)) tail;;

let rev x = revhelper Nil x;;

(*merge sort*)
let rec halve lst = match lst with 
	Nil -> Nil, Nil
	| Cons(a, Nil) as t -> t, Nil
	| Cons(a, Cons(b, lst)) -> let lst1, lst2 = halve lst in
								Cons(a, lst1), Cons(b, lst2);;

 let rec merge = function
	| a, Nil -> a
	| Nil, b -> b
	| Cons(a, at), Cons(b, bt) ->
	if a <= b then Cons (a, merge(at, Cons(b, bt)))
				else Cons (b, merge(Cons(a, at), bt));;

let rec merge_sort = function 
	| Nil as ret -> ret
	| Cons(_, Nil) as ret -> ret
	| lst -> let (part1, part2) = halve lst in
		merge(merge_sort part1, merge_sort part2);;

let rec print_list = function
	| Nil -> print_string "\n"
	| Cons(element, tail) ->
	 print_int element; print_string " "; (print_list tail);;



(* print_list (merge_sort (Cons (89, Cons(100, Cons(10, Cons(156, Cons(-456, Nil)))))));;
 *)

let lambda_of_string expr = 
	let pos = ref 0 in

	let next () = (pos := !pos + 1) in 
	
	let cchar () = if !pos < (String.length expr) then (String.get expr !pos) 
													else '!' in

	let is_letter x = (('a' <= x) && (x <= 'z')) in
	
	let rec var () = 
		let x = cchar () in
		if is_letter x then (Char.escaped x) ^ (next (); var ()) else "" in
	
	let rec lambda () = 
		let temp = match cchar() with
		| '\\' ->
		  let a = next(); var() in
		  let b = (assert (cchar() = '.')); next(); lambda() in
		  Abs(a, b) 

		| '(' -> let ret = next (); lambda () in (assert (cchar() = ')')); next (); ret
		| x -> if is_letter x then Var (var ())
								else failwith "invalid expression!" in

		if ((is_letter (cchar ()) = false) && (cchar() != '(') && (cchar() != '\\')) 
			then temp else App(temp, lambda ()) in
	
	lambda ();;


let rec string_of_lambda = function 
	| Var x -> x
	| Abs (x, y) -> "(" ^ "\\" ^ x ^ "." ^ (string_of_lambda y) ^ ")"
	| App (x, y) -> "(" ^ (string_of_lambda x) ^ (string_of_lambda y) ^ ")";;

(* let var = 10;;
print_int var;; *)


(* 
print_string (string_of_lambda (Abs("x", Var("x"))));;
print_string "\n";;
print_string (string_of_lambda (Var "x"));; 
 

print_string (string_of_lambda (lambda_of_string "\\x.(\\y.(a(b)))"));;


 print_string "\n";;*)