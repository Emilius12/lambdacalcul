type variable = Var of char;;
type terme = V of variable | App of terme*terme | Lamb of variable*terme;;


let var (x: terme) =  match x with  (* permet de passer d'un terme à la variable correspondante*)
V(c) -> c;
|_ -> failwith "pas une variable";;

