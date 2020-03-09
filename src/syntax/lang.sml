structure Syntax : sig
  type var = string
  type regionvar = string
  type pointername = int
  type regionset = regionvar Set.set
  type effect = regionvar Set.set
  type operator = string

  datatype ty =
    IntTy
  | BoolTy
  | UnitTy
  | TupleTy of ty list
  | FuncTy of ty list * ty * effect
  | RegFuncTy of regionvar * ty * effect
  | BoxedTy of ty * regionvar

  and value =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  | Lambda of regionset * var list * term * ty list
  | Tuple of term list
  | BarePointer of regionvar * pointername

  and term = 
    Value of value
  | Var of var
  | Select of int * term
  | Box of term * regionvar
  | Unbox of term
  | Let of var * term * term * ty
  | LetRegion of regionvar * term
  | RegionElim of regionset * term
  | IfElse of term * term * term
  | App of term * term list
  | PrimApp of operator * term * term

  and declaration = 
    DeclType of regionset * var * ty
  | DeclVal of var * ty * term
  | DeclFun of var * var list * ty list * ty * term

  and program = 
    Prog of declaration list

  val substRegVarTy : (regionvar * regionvar) -> ty -> ty
  val substRegVar : (regionvar * regionvar) -> term -> term
  val substRegVarValue : (regionvar * regionvar) -> value -> value
end
=
struct
  type var = string
  type regionvar = string
  type pointername = int
  type regionset = regionvar Set.set
  type effect = regionvar Set.set
  type operator = string

  datatype ty =
    IntTy
  | BoolTy
  | UnitTy
  | TupleTy of ty list
  | FuncTy of ty list * ty * effect
  | RegFuncTy of regionvar * ty * effect
  | BoxedTy of ty * regionvar

  and value =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  | Lambda of regionset * var list * term * ty list
  | Tuple of term list
  | BarePointer of regionvar * pointername

  and term = 
    Value of value
  | Var of var
  | Select of int * term
  | Box of term * regionvar
  | Unbox of term
  | Let of var * term * term * ty
  | LetRegion of regionvar * term
  | RegionElim of regionset * term
  | IfElse of term * term * term
  | App of term * term list
  | PrimApp of operator * term * term

  and declaration = 
    DeclType of regionset * var * ty
  | DeclVal of var * ty * term
  | DeclFun of var * var list * ty list * ty * term

  and program = 
    Prog of declaration list

  fun substRegVarTy (dst, newr) (IntTy) = IntTy
  | substRegVarTy (dst, newr) (BoolTy) = BoolTy
  | substRegVarTy (dst, newr) (UnitTy) = UnitTy
  | substRegVarTy (dst, newr) (TupleTy t) = 
      TupleTy (map (substRegVarTy (dst, newr)) t)
  | substRegVarTy (dst, newr) (FuncTy (t1, t2, phi)) =
      FuncTy (map (substRegVarTy (dst, newr)) t1, 
        substRegVarTy (dst, newr) t2,
        map (fn r => if dst = r then newr else r) phi)
  | substRegVarTy (dst, newr) (RegFuncTy (rv, t, phi)) =
      RegFuncTy (rv, substRegVarTy (dst, newr) t,
        map (fn r => if dst = r then newr else r) phi)
  | substRegVarTy (dst, newr) (BoxedTy (t, r)) = 
      BoxedTy (substRegVarTy (dst, newr) t, if dst = r then newr else r)

  fun substRegVar (dst, newr) (Value v) = Value (substRegVarValue (dst, newr) v)
  | substRegVar (dst, newr) (Var v) = Var v
  | substRegVar (dst, newr) (Select (i, m)) =
      Select (i, substRegVar (dst, newr) m)
  | substRegVar (dst, newr) (Box (m, r)) = 
      Box (substRegVar (dst, newr) m, if dst = r then newr else r)
  | substRegVar (dst, newr) (Unbox m) = 
      Unbox (substRegVar (dst, newr) m)
  | substRegVar (dst, newr) (Let (x, m1, m2, argt)) = 
      Let (x, substRegVar (dst, newr) m1, substRegVar (dst, newr) m2, argt)
  | substRegVar (dst, newr) (LetRegion (r, m)) = 
      LetRegion (r, substRegVar (dst, newr) m)
  | substRegVar (dst, newr) (IfElse (m1, m2, m3)) = 
      IfElse (substRegVar (dst, newr) m1, substRegVar (dst, newr) m2, substRegVar (dst, newr) m3)
  | substRegVar (dst, newr) (RegionElim (rs, m)) = 
      RegionElim (map (fn r => if dst = r then newr else r) rs, substRegVar (dst, newr) m)
  | substRegVar (dst, newr) (App (m1, m2)) = 
      App (substRegVar (dst, newr) m1, map (substRegVar (dst, newr)) m2)
  | substRegVar (dst, newr) (PrimApp (opr, m1, m2)) = 
      PrimApp (opr, substRegVar (dst, newr) m1, substRegVar (dst, newr) m2)

  and substRegVarValue (dst, newr) (IntLit i) = IntLit i
  | substRegVarValue (dst, newr) (BoolLit b) = BoolLit b
  | substRegVarValue (dst, newr) (UnitLit) = UnitLit
  | substRegVarValue (dst, newr) (Lambda (rs, x, m, argt)) = 
      Lambda (rs, x, substRegVar (dst, newr) m, map (substRegVarTy (dst, newr)) argt)
  | substRegVarValue (dst, newr) (Tuple m) = 
      Tuple (map (substRegVar (dst, newr)) m)
  | substRegVarValue (dst, newr) (BarePointer (r, p)) = (BarePointer (r, p))
end

