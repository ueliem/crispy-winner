structure Lang : sig
  type var = string
  type regionvar = string
  type pointername = int
  type effect = regionvar Set.set
  type operator = string

  datatype boxty = 
    BoxIntTy of regionvar
  | BoxBoolTy of regionvar
  | BoxUnitTy of regionvar
  | BoxTupleTy of ty * ty * regionvar
  | BoxFuncTy of ty * ty * effect * regionvar
  | BoxRegFuncTy of regionvar * ty * effect * regionvar

  and ty =
    IntTy
  | BoolTy
  | UnitTy
  | TupleTy of ty * ty
  | BoxedTy of boxty

  datatype abs = 
    Lambda of var * term * ty * regionvar
  | RegionLambda of regionvar * abs * regionvar
  
  and value =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  | Tuple of term * term
  | BarePointer of regionvar * pointername

  and boxvalue = 
    BoxIntLit of int * regionvar
  | BoxBoolLit of bool * regionvar
  | BoxUnitLit of regionvar
  | BoxAbs of abs
  | BoxTuple of term * term * regionvar
  | BoxBarePointer of regionvar * pointername * regionvar

  and term = 
    Value of value
  | BoxedValue of boxvalue
  | Var of var
  | First of term
  | Second of term
  | Unbox of term
  | Let of var * term * term * ty
  | LetRegion of regionvar * term
  | RegionElim of term * regionvar
  | IfElse of term * term * term
  | App of term * term
  | PrimApp of operator * term * term

  val substRegVarBoxTy : (regionvar * regionvar) -> boxty -> boxty
  val substRegVarTy : (regionvar * regionvar) -> ty -> ty
  val substRegVar : (regionvar * regionvar) -> term -> term
  val substRegVarValue : (regionvar * regionvar) -> value -> value
  val substRegVarBoxValue : (regionvar * regionvar) -> boxvalue -> boxvalue
  val substRegVarAbs : (regionvar * regionvar) -> abs -> abs

  val isValue : term -> bool
end
=
struct
  type var = string
  type regionvar = string
  type pointername = int
  type effect = regionvar Set.set
  type operator = string

  datatype boxty = 
    BoxIntTy of regionvar
  | BoxBoolTy of regionvar
  | BoxUnitTy of regionvar
  | BoxTupleTy of ty * ty * regionvar
  | BoxFuncTy of ty * ty * effect * regionvar
  | BoxRegFuncTy of regionvar * ty * effect * regionvar

  and ty =
    IntTy
  | BoolTy
  | UnitTy
  | TupleTy of ty * ty
  | BoxedTy of boxty

  datatype abs = 
    Lambda of var * term * ty * regionvar
  | RegionLambda of regionvar * abs * regionvar

  and value =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  | Tuple of term * term
  | BarePointer of regionvar * pointername

  and boxvalue = 
    BoxIntLit of int * regionvar
  | BoxBoolLit of bool * regionvar
  | BoxUnitLit of regionvar
  | BoxAbs of abs
  | BoxTuple of term * term * regionvar
  | BoxBarePointer of regionvar * pointername * regionvar

  and term = 
    Value of value
  | BoxedValue of boxvalue
  | Var of var
  | First of term
  | Second of term
  | Unbox of term
  | Let of var * term * term * ty
  | LetRegion of regionvar * term
  | RegionElim of term * regionvar
  | IfElse of term * term * term
  | App of term * term
  | PrimApp of operator * term * term

  fun substRegVarBoxTy (dst, newr) (BoxIntTy rho) = 
      BoxIntTy (if dst = rho then newr else rho)
  | substRegVarBoxTy (dst, newr) (BoxBoolTy rho) = 
      BoxBoolTy (if dst = rho then newr else rho)
  | substRegVarBoxTy (dst, newr) (BoxUnitTy rho) = 
      BoxUnitTy (if dst = rho then newr else rho)
  | substRegVarBoxTy (dst, newr) (BoxTupleTy (t1, t2 , rho)) = 
      BoxTupleTy (substRegVarTy (dst, newr) t1, 
        substRegVarTy (dst, newr) t2,
        if dst = rho then newr else rho)
  | substRegVarBoxTy (dst, newr) (BoxFuncTy (t1, t2, phi, rho)) =
      BoxFuncTy (substRegVarTy (dst, newr) t1, 
        substRegVarTy (dst, newr) t2,
        map (fn r => if dst = r then newr else r) phi,
        if dst = rho then newr else rho)
  | substRegVarBoxTy (dst, newr) (BoxRegFuncTy (rv, t, phi, rho)) =
      BoxRegFuncTy (rv, substRegVarTy (dst, newr) t,
        map (fn r => if dst = r then newr else r) phi,
        if dst = rho then newr else rho)

  and substRegVarTy (dst, newr) (IntTy) = IntTy
  | substRegVarTy (dst, newr) (BoolTy) = BoolTy
  | substRegVarTy (dst, newr) (UnitTy) = UnitTy
  | substRegVarTy (dst, newr) (TupleTy (t1, t2)) = 
      TupleTy (substRegVarTy (dst, newr) t1, substRegVarTy (dst, newr) t2)
  | substRegVarTy (dst, newr) (BoxedTy t) = 
      BoxedTy (substRegVarBoxTy (dst, newr) t)

  fun substRegVar (dst, newr) (Value v) = Value (substRegVarValue (dst, newr) v)
  | substRegVar (dst, newr) (BoxedValue v) = 
      BoxedValue (substRegVarBoxValue (dst, newr) v)
  | substRegVar (dst, newr) (Var v) = Var v
  | substRegVar (dst, newr) (First (m)) =
      First (substRegVar (dst, newr) m)
  | substRegVar (dst, newr) (Second (m)) =
      Second (substRegVar (dst, newr) m)
  | substRegVar (dst, newr) (Unbox m) = 
      Unbox (substRegVar (dst, newr) m)
  | substRegVar (dst, newr) (Let (x, m1, m2, argt)) = 
      Let (x, substRegVar (dst, newr) m1, substRegVar (dst, newr) m2, argt)
  | substRegVar (dst, newr) (LetRegion (r, m)) = 
      LetRegion (r, substRegVar (dst, newr) m)
  | substRegVar (dst, newr) (IfElse (m1, m2, m3)) = 
      IfElse (substRegVar (dst, newr) m1, substRegVar (dst, newr) m2, substRegVar (dst, newr) m3)
  | substRegVar (dst, newr) (RegionElim (m, r)) = 
      RegionElim (substRegVar (dst, newr) m, r)
  | substRegVar (dst, newr) (App (m1, m2)) = 
      App (substRegVar (dst, newr) m1, substRegVar (dst, newr) m2)
  | substRegVar (dst, newr) (PrimApp (opr, m1, m2)) = 
      PrimApp (opr, substRegVar (dst, newr) m1, substRegVar (dst, newr) m2)

  and substRegVarValue (dst, newr) (IntLit i) = IntLit i
  | substRegVarValue (dst, newr) (BoolLit b) = BoolLit b
  | substRegVarValue (dst, newr) (UnitLit) = UnitLit
  | substRegVarValue (dst, newr) (Tuple (m1, m2)) = 
      Tuple (substRegVar (dst, newr) m1, substRegVar (dst, newr) m2)
  | substRegVarValue (dst, newr) (BarePointer (r, p)) = (BarePointer (r, p))

  and substRegVarBoxValue (dst, newr) (BoxIntLit (i, r)) = BoxIntLit (i, if dst = r then newr else r)
  | substRegVarBoxValue (dst, newr) (BoxBoolLit (b, r)) = BoxBoolLit (b, if dst = r then newr else r)
  | substRegVarBoxValue (dst, newr) (BoxUnitLit r) = BoxUnitLit (if dst = r then newr else r)
  | substRegVarBoxValue (dst, newr) (BoxAbs a) = BoxAbs (substRegVarAbs (dst, newr) a)
  | substRegVarBoxValue (dst, newr) (BoxTuple (m1, m2, r)) = 
      BoxTuple (substRegVar (dst, newr) m1, substRegVar (dst, newr) m2, if dst = r then newr else r)
  | substRegVarBoxValue (dst, newr) (BoxBarePointer (r1, p, r2)) =
      BoxBarePointer (r1, p, if dst = r2 then newr else r2)

  and substRegVarAbs (dst, newr) (Lambda (x, m, argt, r)) = 
      Lambda (x, substRegVar (dst, newr) m, argt, if dst = r then newr else r)
  | substRegVarAbs (dst, newr) (RegionLambda (r1, m, r2)) = 
      RegionLambda (r1, substRegVarAbs (dst, newr) m, if dst = r2 then newr else r2)

  fun isValue (Value _) = true
  | isValue (BoxedValue _) = false
  | isValue (Var _) = false
  | isValue (First _) = false
  | isValue (Second _) = false
  | isValue (Unbox _) = false
  | isValue (Let _) = false
  | isValue (LetRegion _) = false
  | isValue (RegionElim _) = false
  | isValue (IfElse _) = false
  | isValue (App _) = false
  | isValue (PrimApp _) = false
end

