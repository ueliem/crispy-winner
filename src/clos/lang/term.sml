structure ClosTerm :
sig
  datatype var =
    NamedVar of string
  | GenVar of int
  datatype operator = string
  datatype sort =
    TypeVal
  | KindVal
  | TypeComp
  | KindComp
  val ax = [(TypeVal, KindVal), (CompVal, KindVal)]
  datatype tcon =
    TyConNamed of string
  | TyConTuple
  | TyConInt
  | TyConBool
  | TyConUnit
  datatype ty =
    TyVar of string
  | TyApp of ty list * tcon
  | TyComp of ty
  datatype term =
    Var of var
  | Sort of sort
  | App of term * term
  | PrimApp of operator * term list
  | IfElse of term * term * term
  | Let of var * term * term * term
  | Return of term
  | M of term
  | IntLit of int
  | BoolLit of bool
  | UnitLit
  | Lambda of var * term * term
  | DepProduct of var * term * term
  | Fix of var * term * term
  | Tuple of term list

end
=
struct
end

