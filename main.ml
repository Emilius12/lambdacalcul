type variable = Var of char

type terme = V of variable | App of terme*terme | Lamb of variable*terme

let estvariable (x:terme) = match x with |V(_) -> true ; |_-> false

let var (x: terme) =  match x with  (* permet de passer d'un terme à la variable correspondante*)
|V(c) -> c;
|_ -> failwith "pas une variable"


let get_var (x:terme) : char list = (* recupere la liste des variables utilisees dans le terme *)
  let rec construct = function
      | V(Var c) -> [c]
      | App(y,z) -> (construct y) @ (construct z)
      | Lamb(Var(c),y) -> c::(construct y)
  in
  List.fold_left (fun m x -> if List.mem x m then x::m else m) [] (construct x) (* filtre la liste pour avoir des variables distinctes *)


let conflict_var (x:terme) (y:terme) = (* est-ce qu'une variable dans y coincide avec une de x ? *)
  let rec aux l1 l2 = match l2 with
      | [] -> false
      | x::q -> (List.mem x l1) || (aux l1 q)
  in
  aux (get_var x) (get_var y)


let rec subs (x:terme) (a:char) (b:terme) = (*substitue toutes les occurrences de a par b dans x, attention la variable a 
ne doit pas se trouver juste aprÃ¨s un lambda et b ne doit pas etre un nom deja utilise*) 
  match x with
  |V(Var(c)) ->( match c = a with |true -> b |_ -> V(Var(c)););
  |App(y,z) -> if conflict_var y b || conflict_var z b then failwith "variable de substitution deja presente"
               else App(subs y a b, subs z a b)
  |Lamb(Var(c),y) -> match c = a with
                     | true -> x
                     | _ -> if conflict_var y b then failwith "variable de substitution deja  presente"
                            else Lamb(Var(c),subs y a b)


let alpha_red (x:terme) (a:char) (b:char) = (* effectue l'alpha conversion de x, la variable b ne doit pas etre deja utilise *)
match x with
|Lamb(Var(c),y) when c = a -> if conflict_var y (V(Var b)) then failwith "variable de substitution deja presente"
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
                      | _ -> failwith "erreur non evaluee")
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


let rec normalisation_gauche (x:terme) = (* normalise un terme jusqu'a ne plus avoir de redex *)
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
(* Strategie: on fait du backtracking sur les possibilitÃ©s de reduction *)
(* on construit d'abord le terme correspondant a la beta reduction du i-eme redex *)
  let rec parcours_terme (x:terme) (cnt:int) = match x with
      | App(Lamb(Var _,y),z) when cnt=0 -> x, beta_red x
      | App(Lamb(Var c,y),z) -> if cnt<=(cnt_redex y) then x, App(Lamb(Var c,snd (parcours_terme y (cnt-1))),z) else x, App(Lamb(Var c,y),snd (parcours_terme z (cnt-1)))
      | _ -> x,x
  in

(* on evalue ensuite pour chaque possibilite (backtracking) que toute normalisation retombe sur une forme normale *)
  let rec parcours_backtracking (x:terme) =
    if cnt_redex x = 0 then true
    else (match x with
            | App(Lamb(Var _,_),_) -> let l = List.init (cnt_redex x) (fun i -> parcours_terme x i)  in
                                      List.fold_left (fun m x -> not (fst x = snd x && countains_redex (fst x)) && parcours_backtracking (snd x) && m) true l(* on vÃ©rifie qu'on n'a pas de point fixe suite a une beta-reduction, sinon boucle pour une normalisation, puis on avance tant qu'il existe plus d'un redex *)
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
(* Strategie: on fait du backtracking sur les possibilitÃ©s de rÃ©duction *)
(* on construit d'abord le terme correspondant a la beta reduction du i-eme redex *)
  let rec parcours_terme (x:terme) (cnt:int) = match x with
      | App(Lamb(Var _,y),z) when cnt=0 -> x, beta_red x
      | App(Lamb(Var c,y),z) -> if cnt<=(cnt_redex y) then x, App(Lamb(Var c,snd (parcours_terme y (cnt-1))),z) else x, App(Lamb(Var c,y),snd (parcours_terme z (cnt-1)))
      | _ -> x,x
  in

(* on evalue ensuite pour chaque possibilite (backtracking) qu'une normalisation retombe sur une forme normale *)
  let rec parcours_backtracking (x:terme) =
    if cnt_redex x = 0 then true,x
    else (match x with
            | App(Lamb(Var _,_),_) -> let l = List.init (cnt_redex x) (fun i -> parcours_terme x i)  in
                                      List.fold_left (fun m x -> let new_x = parcours_backtracking (snd x) in
                                                                 (not (fst x = snd x && countains_redex (fst x)) && fst new_x) || fst m, if not (countains_redex (snd new_x)) then snd new_x else snd m) (false,x) l(* on verifie qu'on n'a pas de point fixe suite a une beta-reduction, sinon boucle pour une normalisation, et on regarde si on a un candidat *)
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

(* let t1 = church_rec 3 *)




(* λ-calcul simplement type *)
type typeV = A of int | Func of typeV * typeV

type preterme = V of variable | App of preterme*preterme | Lamb of (variable*typeV)*preterme

type typage = preterme * typeV

type contexte = (preterme, typeV) Hashtbl.t

type jugement = contexte * typage

type regle = VAR | APP | ABS

type arbre = Nil | N1 of jugement*regle*arbre | N2 of jugement*regle*arbre*arbre

exception RuleError of string
exception DerivationError of string

let variables_libres (x:terme) : variable list = (* cherche variables libres dans un terme *)
  let rec find (x:terme) (liee:variable list) = match x with
      | V(c) -> if not (List.mem c liee) then [c]
                else []
      | App(y,z) -> (find y liee) @ (find z liee)
      | Lamb(c,y) -> find y (c::liee)
  in
  find x []



(*(*(*(* fonctions à utiliser pour l'inférence de type à un terme *)*)*)*)


(* let rec supp_contexte (x:typage) (gamma:contexte) = match gamma with *)
(*     | [] -> [] *)
(*     | t::q -> if t = x then q else t::(supp_contexte x q) *)


(* (\* regles typage *\) *)
(* let regle_var (gamma:contexte) (x:typage) : jugement = match x with *)
(*     | V(Var c), alpha when List.mem x gamma -> gamma, x *)
(*     | _ -> raise (RuleError "variable") *)


(* let regle_app (type1:jugement) (type2:jugement) : jugement = match type1, type2 with *)
(*     | (gamma1,(y,Func(alpha1,tau))), (gamma2,(z,alpha2)) when gamma1 = gamma2 && alpha1 = alpha2 -> gamma1, (App(y,z),tau) *)
(*     | _ -> raise (RuleError "application") *)


(* let regle_abs (jug:jugement) (x:typage) : jugement = match jug, x with *)
(*     | (gamma,(y,tau)),(V(Var c),alpha) when List.mem x gamma -> (supp_contexte x gamma), (Lamb((Var c,alpha),y),Func(alpha,tau)) *)
(*     | _ -> raise (RuleError "abstraction") *)


let rec print_type (t:typeV) = match t with
    | A n -> Printf.printf "%d" n
    | Func(t1,t2) -> Printf.printf "(";
                     print_type t1;
                     Printf.printf " -> ";
                     print_type t2;
                     Printf.printf ")"


let print_preterme (x:preterme) =
  let rec print_terme (x:preterme) = match x with
    | V(Var c) -> Printf.printf "%c" c
    | App(y,z) -> Printf.printf "(";
                  print_terme y;
                  Printf.printf ")(";
                  print_terme z;
                  Printf.printf ")";
    | Lamb((Var c,t),App(y,z)) -> Printf.printf "λ(%c : " c;
                                  print_type t;
                                  Printf.printf ").";
                                  print_terme y;
                                  print_terme z
    | Lamb((Var c,t),y) -> Printf.printf "λ(%c : " c;
                           print_type t;
                           Printf.printf ").";
                           print_terme y
  in print_terme x


let print_jug (jug:jugement) = match jug with
    | gamma, (y,t) -> Printf.printf "Γ |- ";
                        print_preterme y;
                        Printf.printf " : ";
                        print_type t


let print_regle (r:regle) = match r with
    | VAR -> Printf.printf "VAR"
    | APP -> Printf.printf "APP"
    | ABS -> Printf.printf "ABS"


let rec print_arbre (a:arbre) = match a with
    | Nil -> ()
    | N1(jug,r,a2) -> print_jug jug;
                      print_newline ();
                      print_newline ();
                      print_regle r;
                      Printf.printf "-----------------------------\n";
                      print_arbre a2
    | N2(jug,r,a2,a3) -> print_jug jug;
                         print_newline ();
                         print_newline ();
                         print_regle r;
                         Printf.printf "-----------------------------\n";
                         print_arbre a2;
                         print_arbre a3


let rec derivation (jug:jugement) : arbre = match jug with
(* construction arbre de verification de type d'un typage *)
  | gamma, (V(Var c),alpha) -> if Hashtbl.find gamma (V(Var c)) = alpha then
                                 N1(jug,VAR,Nil)
                               else raise (DerivationError "variable incompatible contexte")
  | gamma, (App(y,z),alpha) -> if Hashtbl.mem gamma z then
                                 N2(jug, APP, derivation (gamma,(y,Func(Hashtbl.find gamma z,alpha))), derivation (gamma,(z,Hashtbl.find gamma z)))
                               else raise (DerivationError "Application impossible")
  | gamma, (Lamb((Var c,alpha1),y),Func(alpha2,tau)) when alpha1 = alpha2 -> let new_gamma = Hashtbl.copy gamma in
                                          Hashtbl.add new_gamma (V(Var c)) alpha1;
                                          N1(jug, ABS, derivation (new_gamma,(y,tau)))
  | gamma, (Lamb((Var c,alpha1),y),_) -> raise (DerivationError "Abstraction incompatible par types")


(* exemple du cours *)
(* let a1 = derivation (Hashtbl.create 17, (Lamb((Var 'f',Func(A 2,Func(A 1,A 3))),Lamb((Var 'x',A 1),Lamb((Var 'y',A 2),App(App(V(Var 'f'),V(Var 'y')),V(Var 'x'))))),Func(Func(A 2,Func(A 1,A 3)),Func(A 1,Func(A 2,A 3))))) *)
(* let _ = print_arbre a1 *)



(*(*(* Algorithme Hindley-Milner *)*)*)


let rec desannot (x:preterme) : terme = match x with (* enleve les types dans les abstractions du lambda-CST *)
    | V(Var c) -> V(Var c)
    | App(y,z) -> App(desannot y,desannot z)
    | Lamb((Var c,_),y) -> Lamb(Var c,desannot y)


let rec type_is_in (t1:typeV) (t2:typeV) = match t1, t2 with (* type present dans un autre *)
    | A n, A m -> n = m
    | _, Func(t3,t4) -> type_is_in t1 t3 || type_is_in t1 t4
    | _ -> false


let rec replace_type t1 t2 t3 = match t1,t2 with (* on remplace dans t1 le type variable t2 par t3 *)
    | A n,A m when n = m -> t3
    | A n,A m -> t1
    | Func(t5,t6),_ -> Func (replace_type t5 t2 t3,replace_type t6 t2 t3)
    | _ -> failwith "incompatibilite des types pour substitution"


let get_constraints (x:preterme) = (* recupere types associes aux variables et contraintes sur ces derniers *)
  let cnt = ref (-1) in (* types pour les variables fraiches *)
  let var = Hashtbl.create 17 in (* types frais variables *)
  let const = Hashtbl.create 17 in (* contraintes *)
  let rec build (x:terme) = match x with
      | V(_) -> Hashtbl.find var x
      | App(y,z) -> incr cnt;
                    let n = !cnt in
                    Hashtbl.add const (build y) (Func(build z,A n));
                    A n
      | Lamb(Var c,y) -> incr cnt;
                         let n = !cnt in
                         Hashtbl.add var (V(Var c)) (A n);
                         Func(A n,build y)
  in
  let x' = desannot x in
  let type_final = build x' in
  incr cnt;
  Hashtbl.add const (A !cnt) type_final; (* on rajoute le type final pour la substitution finale plus tard *)
  x',var,const,A !cnt


let resol_by_uni const type_final = (* deuxieme etape algo: unification des contraintes *)
  let subst = Hashtbl.create 17 in (* substitutions de types *)
  let rec deduct h = (* remplit la table des substitutions a partir des contraintes *)
    Hashtbl.iter (fun v s -> if Hashtbl.mem h v then Hashtbl.replace h v s) subst; (* substitution dans les contraintes *)
    if Hashtbl.length h = 0 then ()
    else(
      Hashtbl.iter (fun zeta1 zeta2 -> Hashtbl.remove h zeta1; (* on enleve la contrainte actuelle *)
                                       (match zeta1,zeta2 with
                                        | _, _ when zeta1 = zeta2 -> ()
                                        | A n, _ when not (type_is_in zeta1 zeta2) -> Hashtbl.add subst zeta1 zeta2
                                        | _, A m when not (type_is_in zeta2 zeta1) -> Hashtbl.add subst zeta2 zeta1
                                        | Func(k1,x1), Func(k2,x2) -> Hashtbl.add h k1 k2;
                                                                      Hashtbl.add h x1 x2;
                                        | _ -> failwith "incompatibilité de types")) h;
      deduct h)
  in
  deduct const;
  subst


let rec reconstruct (x:terme) (var:(terme,typeV) Hashtbl.t) subst : preterme = match x with (* reconstruction d'un typage en lambda-cst *)
    | V(Var c) -> V(Var c)
    | App(y,z) -> App(reconstruct y var subst,reconstruct z var subst)
    | Lamb(Var c,y) -> Lamb((Var c,if Hashtbl.mem subst (Hashtbl.find var (V(Var c))) then Hashtbl.find subst (Hashtbl.find var (V(Var c))) else Hashtbl.find var (V(Var c))),reconstruct y var subst)


let hindley_milner (x:preterme) =
  let x', var, const, type_final = get_constraints x in
  let subst = resol_by_uni const type_final in
  Hashtbl.iter (fun t1 t2 -> (Hashtbl.iter (fun t3 t4 -> if (t1 != t3 || t2 != t4) && type_is_in t1 t4 then (
                                                           Hashtbl.replace subst t3 (replace_type t4 t1 t2);
                                                           Hashtbl.remove subst t1)) subst)) subst;
  reconstruct x' var subst, Hashtbl.find subst type_final




(* Exemples du cours *)

(* let a1 = Lamb((Var 'f',Func(A 2,Func(A 1,A 3))),Lamb((Var 'x',A 1),Lamb((Var 'y',A 2),App(App(V(Var 'f'),V(Var 'y')),V(Var 'x'))))) *)
(* let t1 = hindley_milner a1 *)
(* let a2 = Lamb((Var 'x',A 0),Lamb((Var 'y',A 1),V(Var 'x'))) *)
(* let a3 = Lamb((Var 'z',A 2),Lamb((Var 'u',A 3),V(Var 'z'))) *)
(* let a4 = App(a2,a3) *)
(* let t2 = hindley_milner a4 *)
