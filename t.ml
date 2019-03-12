open Hw1;;

(* ocamlc hw1.ml hw1.mli t.ml -o t.exe *)

print_int (int_of_peano (inc (peano_of_int 1)));;
print_string "\n";;
print_int (int_of_peano (inc (peano_of_int 9999)));;
print_string "\n";;
print_int (int_of_peano (add (peano_of_int 30) (peano_of_int 12)));;
print_string "\n";;
print_int (int_of_peano (sub (peano_of_int 29) (peano_of_int 19)));;
print_string "\n";;
print_int (int_of_peano (mul (peano_of_int 1000) (peano_of_int 30)));;
print_string "\n";;
print_int (int_of_peano (div (peano_of_int 144) (peano_of_int 12)));;
print_string "\n";;
print_int (int_of_peano (power (peano_of_int 2) (peano_of_int 10)));;
print_string "\n";;