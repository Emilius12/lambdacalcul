type variable = Var of char

type terme = V of variable | App of terme*terme | Lamb of variable*terme

let estvariable (x:terme) = match x with |V(_) -> true ; |_-> false

let var (x: terme) =  match x with  (* permet de passer d'un terme Ã  la variable correspondante*)
|V(c) -> c;
|_ -> failwith "pas une variable"


let get_var (x:terme) : char list = (* rÃ©cupÃ¨re la liste des variables utilisÃ©es dans le terme *)
  let rec construct = function
      | V(Var c) -> [c]
      | App(y,z) -> (construct y) @ (construct z)
      | Lamb(Var(c),y) -> c::(construct y)
  in
  List.fold_left (fun m x -> if List.mem x m then x::m else m) [] (construct x) (* filtre la liste pour avoir des variables distinctes *)


let conflict_var (x:terme) (y:terme) = (* est-ce qu'une variable dans y coÃ¯ncide avec une de x ? *)
  let rec aux l1 l2 = match l2 with
      | [] -> false
      | x::q -> (List.mem x l1) || (aux l1 q)
  in
  aux (get_var x) (get_var y)


let rec subs (x:terme) (a:char) (b:terme) = (*substitue toutes les occurrences de a par b dans x, attention la variable a 
ne doit pas se trouver juste aprÃ¨s un lambda et b ne doit pas Ãªtre un nom dÃ©jÃ  utilisÃ©*) 
  match x with
  |V(Var(c)) ->( match c = a with |true -> b |_ -> V(Var(c)););
  |App(y,z) -> if conflict_var y b || conflict_var z b then failwith "variable de substitution dÃ©jÃ  prÃ©sente"
               else App(subs y a b, subs z a b)
  |Lamb(Var(c),y) -> match c = a with
                     | true -> x
                     | _ -> if conflict_var y b then failwith "variable de substitution dÃ©jÃ  prÃ©sente"
                            else Lamb(Var(c),subs y a b)


let alpha_red (x:terme) (a:char) (b:char) = (* effectue l'alpha conversion de x, la variable b ne doit pas Ãªtre dÃ©jÃ  utilisÃ©e *)
match x with
|Lamb(Var(c),y) when c = a -> if conflict_var y (V(Var b)) then failwith "variable de substitution dÃ©jÃ  prÃ©sente"
                              else Lamb(Var(b), subs y a (V(Var b)));
|_ -> x


let rec countains_redex (x:terme) = match x with (* terme de la forme (Lamb(x).y)z *)
    | V(Var c) -> false
    | App(Lamb(Var _,y),z) -> true
    | App(y,z) -> countains_redex y || countains_redex z
    | Lamb(Var c,y) -> countains_redex y



let rec beta_red (x:terme) = (* applique une beta reduction *)
  if countains_redex x then (match x with
                      | App(Lamb(Var c,y),App(x,z)) -> App(subs y c x,z)
                      | App(Lamb(Var c,y),z) -> subs y c z
                      | App(x,App(Lamb(Var c,y),App(z1,z2))) -> App(x,App(subs y c z1,z2))
                      | App(x,App(Lamb(Var c,y),z)) -> App(x,subs y c z)
                      | Lamb(Var c,y) when countains_redex y -> Lamb(Var c,beta_red y)
                      | _ -> failwith "erreur non Ã©valuÃ©e")
  else x

let print_terme x =
  print_newline ();
  let rec print_terme (x:terme) = match x with
    | V(Var c) -> Printf.printf "%c" c
    | App(y,z) -> Printf.printf "(";
                  print_terme y;
                  Printf.printf ")(";
                  print_terme z;
                  Printf.printf ")";
    | Lamb(Var c,App(y,z)) -> Printf.printf "λ%c." c;
                              print_terme y;
                              print_terme z
    | Lamb(Var c,y) -> Printf.printf "λ%c." c;
                       print_terme y
  in print_terme x;
     print_newline ()


let rec normalisation_gauche (x:terme) = (* normalise un terme jusqu'Ã  ne plus avoir de redex *)
  print_terme x;
  if not (countains_redex x) then x
  else (
    let new_x = beta_red x in
    if new_x = x then x
    else normalisation_gauche (beta_red x))


let rec cnt_redex = function (* compte le nombre de redex dans le terme *)
    | V(Var c) -> 0
    | App(Lamb(Var _,y),z) -> 1 + cnt_redex y + cnt_redex z
    | App(y,z) -> cnt_redex y + cnt_redex z
    | Lamb(Var c,y) -> cnt_redex y


let rec fortement_normalisable (x:terme) =
(* StratÃ©gie: on fait du backtracking sur les possibilitÃ©s de rÃ©duction *)
(* on construit d'abord le terme correspondant Ã  la beta reduction du i-Ã¨me redex *)
  let rec parcours_terme (x:terme) (cnt:int) = match x with
      | App(Lamb(Var _,y),z) when cnt=0 -> x, beta_red x
      | App(Lamb(Var c,y),z) -> if cnt<=(cnt_redex y) then x, App(Lamb(Var c,snd (parcours_terme y (cnt-1))),z) else x, App(Lamb(Var c,y),snd (parcours_terme z (cnt-1)))
      | _ -> x,x
  in

(* on Ã©value ensuite pour chaque possibilitÃ© (backtracking) que toute normalisation retombe sur une forme normale *)
  let rec parcours_backtracking (x:terme) =
    if cnt_redex x = 0 then true
    else (match x with
            | App(Lamb(Var _,_),_) -> let l = List.init (cnt_redex x) (fun i -> parcours_terme x i)  in
                                      List.fold_left (fun m x -> not (fst x = snd x && countains_redex (fst x)) && parcours_backtracking (snd x) && m) true l(* on vÃ©rifie qu'on n'a pas de point fixe suite Ã  une beta-reduction, sinon boucle pour une normalisation, puis on avance tant qu'il existe plus d'un redex *)
            | _ -> true)
  in

  parcours_backtracking x


(* tests forte normalisation *)

(* let exemple1 = App(Lamb(Var 'x',App(V(Var 'x'),V(Var 'x'))),Lamb(Var 'x',App(V(Var 'x'),V(Var 'x')))) *)
(* let repr1 = print_terme exemple1 *)
(* let norm1 = fortement_normalisable exemple1 *)

(* let exemple2 = App(Lamb(Var 'u',Lamb(Var 'z',V(Var 'u'))),App(Lamb(Var 't',V(Var 't')),Lamb(Var 'x',App(V(Var 'x'),V(Var 'x'))))) *)
(* let repr2 = print_terme exemple2 *)
(* let norm2 = fortement_normalisable exemple2 *)

(* let exemple3 = App(Lamb(Var 'u',Lamb(Var 'z',V(Var 'u'))),App(Lamb(Var 'x',App(V(Var 'x'),V(Var 'x'))),Lamb(Var 'x',App(V(Var 'x'),V(Var 'x'))))) *)
(* let repr3 = print_terme exemple3 *)
(* let norm3 = fortement_normalisable exemple3 *)


let rec faiblement_normalisable (x:terme) =
(* StratÃ©gie: on fait du backtracking sur les possibilitÃ©s de rÃ©duction *)
(* on construit d'abord le terme correspondant Ã  la beta reduction du i-Ã¨me redex *)
  let rec parcours_terme (x:terme) (cnt:int) = match x with
      | App(Lamb(Var _,y),z) when cnt=0 -> x, beta_red x
      | App(Lamb(Var c,y),z) -> if cnt<=(cnt_redex y) then x, App(Lamb(Var c,snd (parcours_terme y (cnt-1))),z) else x, App(Lamb(Var c,y),snd (parcours_terme z (cnt-1)))
      | _ -> x,x
  in

(* on Ã©value ensuite pour chaque possibilitÃ© (backtracking) qu'une normalisation retombe sur une forme normale *)
  let rec parcours_backtracking (x:terme) =
    if cnt_redex x = 0 then true,x
    else (match x with
            | App(Lamb(Var _,_),_) -> let l = List.init (cnt_redex x) (fun i -> parcours_terme x i)  in
                                      List.fold_left (fun m x -> let new_x = parcours_backtracking (snd x) in
                                                                 (not (fst x = snd x && countains_redex (fst x)) && fst new_x) || fst m, if not (countains_redex (snd new_x)) then snd new_x else snd m) (false,x) l(* on vÃ©rifie qu'on n'a pas de point fixe suite Ã  une beta-reduction, sinon boucle pour une normalisation, et on regarde si on a un candidat *)
            | _ -> true,x)
  in

  parcours_backtracking x


(* tests faible normalisation *)

(* let exemple3 = App(Lamb(Var 'u',Lamb(Var 'z',V(Var 'u'))),App(Lamb(Var 'x',App(V(Var 'x'),V(Var 'x'))),Lamb(Var 'x',App(V(Var 'x'),V(Var 'x'))))) *)
(* let repr3 = print_terme exemple3 *)
(* let norm3 = faiblement_normalisable exemple3 *)


let rec iteree (n:int) (f:terme) (x:terme)  = match n with
  |0 -> x;
  |p -> App( f , iteree (n-1) f x ) ;;

let rec church (n:int) = Lamb(Var ('f'),Lamb( Var('x') , iteree n (V(Var('f'))) (V(Var('x')))))


let constr_A = Lamb(Var 'm',Lamb(Var 'g',Lamb(Var 'x',App(V(Var 'g'),App(V(Var 'm'),App(V(Var 'g'),V(Var 'x')))))))


let rec church_rec (n:int) = match n with
    | 0 -> Lamb(Var 'f', Lamb(Var 'x',V(Var 'x')))
    | _ -> normalisation_gauche (App(constr_A,church_rec (n-1)))

let t1 = church_rec 3
