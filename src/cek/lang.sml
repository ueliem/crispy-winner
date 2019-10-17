structure Lang : sig
  type var = string
  type operator = string

  datatype ty =
    IntTy
  | TupleTy of ty * ty
  | FuncTy of ty * ty

  datatype term = 
    IntLit of int 
  | Var of var
  | Lambda of var * term * ty
  | Tuple of term * term
  | First of term
  | Second of term
  | Let of var * term * term * ty
  | IfZero of term * term * term
  | App of term * term
  | PrimApp of operator * term

  val isValue : term -> bool
end
=
struct
  type var = string
  type operator = string

  datatype ty =
    IntTy
  | TupleTy of ty * ty
  | FuncTy of ty * ty

  datatype term = 
    IntLit of int 
  | Var of var
  | Lambda of var * term * ty
  | Tuple of term * term
  | First of term
  | Second of term
  | Let of var * term * term * ty
  | IfZero of term * term * term
  | App of term * term
  | PrimApp of operator * term

  fun isValue (IntLit _) = true
  | isValue (Var _) = false
  | isValue (Lambda _) = true
  | isValue (Tuple (m1, m2)) = (isValue m1) andalso (isValue m2)
  | isValue (First _) = false
  | isValue (Second _) = false
  | isValue (Let _) = false
  | isValue (IfZero _) = false
  | isValue (App _) = false
  | isValue (PrimApp _) = false
end

