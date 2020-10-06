structure Operator :
sig
  datatype iop =
    IOpAdd
  | IOpSub
  | IOpMul
  | IOpDiv
  | IOpGT
  | IOpGE
  | IOpLT
  | IOpLE
  datatype bop =
    BOpAnd
  | BOpOr
  | BOpNot
  datatype operator =
    OpApp
  | OpUnit
  | OpM
  | OpInt of iop
  | OpBool of bop
  | OpSelect of int
end
=
struct
end
structure SimpleTerm :
sig
  type name = string
  datatype tcon =
    TyConNamed of string
  | TyConTuple
  | TyConFun
  | TyConInt
  | TyConBool
  | TyConUnit
  | TyConComp
  datatype ty =
    TyVar of name
  | TyApp of ty list * tcon
  datatype var =
    NamedVar of name
  | GenVar of int
  datatype lit =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  datatype pat =
    PatVar of var
  | PatLit of lit
  | PatCon of var option * pat list
  datatype term =
    Var of var
  | Lit of lit
  | Con of var option * term list
  | App of Operator.operator * term list
  | Lambda of var * term
  | Fix of var * term
  | Let of var * term * term
  | LetRec of (var * term) list * term
  | IfElse of term * term * term
  | Mat of term * (pat * term) list

end
=
struct
end

