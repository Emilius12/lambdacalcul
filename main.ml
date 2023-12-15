type variable = Var of char

type terme = V of variable | App of terme*terme | Lamb of variable*terme


let estvariable (x:terme) = match x with |V(_) -> true ; |_-> false


let var (x: terme) =  match x with  (* permet de passer d'un terme à la variable correspondante*)
|V(c) -> c;
|_ -> failwith "pas une variable"


let get_var (x:terme) : char list = (* récupère la liste des variables utilisées dans le terme *)
  let rec construct = function
      | V(Var c) -> [c]
      | App(y,z) -> (construct y) @ (construct z)
      | Lamb(Var(c),y) -> c::(construct y)
  in
  List.fold_left (fun m x -> if List.mem x m then x::m else m) [] (construct x) (* filtre la liste pour avoir des variables distinctes *)


let conflict_var (x:terme) (y:terme) = (* est-ce qu'une variable dans y coïncide avec une de x ? *)
  let rec aux l1 l2 = match l2 with
      | [] -> false
      | x::q -> (List.mem x l1) || (aux l1 q)
  in
  aux (get_var x) (get_var y)


let rec subs (x:terme) (a:char) (b:terme) = (*substitue toutes les occurrences de a par b dans x, attention la variable a 
ne doit pas se trouver juste après un lambda et b ne doit pas être un nom déjà utilisé*) 
match x with
|V(Var(c)) ->( match c = a with |true -> b |_ -> V(Var(c)););
|App(y,z) -> if conflict_var y b || conflict_var z b then failwith "variable de substitution déjà présente"
             else App(subs y a b, subs z a b)
|Lamb(Var(c),y) -> match c = a with
                     | true -> x
                     | _ -> if conflict_var y b then failwith "variable de substitution déjà présente"
                            else Lamb(Var(c),subs y a b)


let alpha_red (x:terme) (a:char) (b:char) = (* effectue l'alpha conversion de x, la variable b ne doit pas être déjà utilisée *)
match x with
|Lamb(Var(c),y) when c = a -> if conflict_var y (V(Var b)) then failwith "variable de substitution déjà présente"
                              else Lamb(Var(b), subs y a (V(Var b)));
|_ -> x


let is_redex (x:terme) = match x with (* terme de la forme (Lamb(x).y)z *)
    | App(Lamb(_,_),_) -> true
    | _ -> false


let beta_red (x:terme) = (* applique une beta reduction *)
  if is_redex x then (match x with
                      | App(Lamb(Var c,y),z) -> subs y c z
                      | _ -> failwith "erreur non évaluée")
  else x


let rec print_terme (x:terme) = match x with
    | V(Var c) -> Printf.printf "%c" c
    | App(y,z) -> print_terme y;
                  print_terme z;
    | Lamb(Var c,y) -> Printf.printf "(λ%c." c;
                       print_terme y;
                       Printf.printf ")"


let rec normalisation_gauche (x:terme) = (* normalise un terme jusqu'à ne plus avoir de redex *)
  print_terme x;
  print_newline ();
  if not (is_redex x) then x
  else (
    let new_x = beta_red x in
    if new_x = x then x
    else normalisation_gauche (beta_red x))

