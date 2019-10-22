structure Lang : sig
  type var = string
  type regionvar = string
  type regionname = string
  type pointername = int
  type placeholder = string
  type effect = placeholder Set.set
  type operator = string

  datatype ty =
    IntTy
  | BoolTy
  | UnitTy
  | TupleTy of ty * ty
  | FuncTy of ty * ty
  | BoxedTy of ty * regionvar

  datatype value =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  | Lambda of var * term * ty
  | Tuple of term * term

  and term = 
    Value of value
  | BoxedValue of value * regionvar
  | BarePointer of regionname * pointername
  | Var of var
  | First of term
  | Second of term
  | Unbox of term
  | Let of var * term * term * ty
  | LetRegion of regionvar * term
  | IfElse of term * term * term
  | App of term * term
  | PrimApp of operator * term

  val isValue : term -> bool
end
=
struct
  type var = string
  type regionvar = string
  type regionname = string
  type pointername = int
  type placeholder = string
  type effect = placeholder Set.set
  type operator = string

  datatype ty =
    IntTy
  | BoolTy
  | UnitTy
  | TupleTy of ty * ty
  | FuncTy of ty * ty
  | BoxedTy of ty * regionvar

  datatype value =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  | Lambda of var * term * ty
  | Tuple of term * term

  and term = 
    Value of value
  | BoxedValue of value * regionvar
  | BarePointer of regionname * pointername
  | Var of var
  | First of term
  | Second of term
  | Unbox of term
  | Let of var * term * term * ty
  | LetRegion of regionvar * term
  | IfElse of term * term * term
  | App of term * term
  | PrimApp of operator * term

  fun isValue (Value _) = true
  | isValue (BoxedValue _) = false
  | isValue (BarePointer _) = true
  | isValue (Var _) = false
  | isValue (First _) = false
  | isValue (Second _) = false
  | isValue (Unbox _) = false
  | isValue (Let _) = false
  | isValue (LetRegion _) = false
  | isValue (IfElse _) = false
  | isValue (App _) = false
  | isValue (PrimApp _) = false
end

