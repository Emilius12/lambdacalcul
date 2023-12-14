type variable = Var of char;;

type terme = V of variable | App of terme*terme | Lamb of variable*terme;;


let estvariable (x:terme) = match x with |V(c) -> true ; |_-> false;;


let var (x: terme) =  match x with  (* permet de passer d'un terme à la variable correspondante*)
|V(c) -> c;
|_ -> failwith "pas une variable";;

let rec subs (x:terme) (a:char) (b:char) = (*substitue toutes les occurrences de a par b dans x, attention la variable a 
ne doit pas se trouver juste après un lambda et b ne doit pas être un nom déjà utilisé*) 
match x with 
|V(Var(c)) ->( match c = a with |true -> V(Var(b)) |_ -> V(Var(c)););
|App(y,z) -> App ( subs y a b , subs z a b);
|Lamb(Var(c),y) -> (match estvariable x with 
						|true ->( match (Var(c) = var x) with 
									|true -> x;
									|_ -> Lamb(Var(c), subs y a b););
						|_ -> Lamb(Var(c), subs y a b); ) ;;	
						
						
let rec alpha (x:terme) (a:char) (b:char) = (* effectue l'alpha conversion de x, la variable b ne doit pas 
être déjà utilisée *)
match x with
|Lamb(Var(c),y) when c = a -> Lamb(Var(b), subs y a b);
|_ -> x;;

