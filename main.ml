type variable = Var of char;;
type terme = V of variable | App of terme*terme | Lamb of variable*terme;;




let x = V(Var('x'));;
x;;
