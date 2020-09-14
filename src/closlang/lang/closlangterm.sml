structure ClosLangTerm :
sig
  type var = ANFTerm.var
  type operator = string
  datatype value =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  | Closure of term * int * var list
  | Tuple of var list
  and comp =
    Value of value
  | Var of var
  | Select of int * var
  | Box of var * RegionSet.regionvar
  | Unbox of var
  | RegionElim of RegionSet.regionset * var
  | App of var * var list
  | PrimApp of operator * var list
  and term =
    Return of var
  | Let of var * comp * term
  | LetRegion of RegionSet.regionvar * term
  | IfElse of var * term * term

end
=
struct
  type var = ANFTerm.var
  type operator = string
  datatype value =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  | Closure of term * int * var list
  | Tuple of var list
  and comp =
    Value of value
  | Var of var
  | Select of int * var
  | Box of var * RegionSet.regionvar
  | Unbox of var
  | RegionElim of RegionSet.regionset * var
  | App of var * var list
  | PrimApp of operator * var list
  and term =
    Return of var
  | Let of var * comp * term
  | LetRegion of RegionSet.regionvar * term
  | IfElse of var * term * term

end

