structure Term :
sig
  type var = string
  type operator = string
  datatype value =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  | Lambda of RegionSet.regionset * (var * Ty.ty) list * Ty.ty * RegionSet.effect * term
  | Tuple of term list
  and term = 
    Value of value
  | Var of var
  | Select of int * term
  | Box of term * RegionSet.regionvar
  | Unbox of term
  | Let of var * term * term * Ty.ty
  | LetRegion of RegionSet.regionvar * term
  | RegionElim of RegionSet.regionset * term
  | IfElse of term * term * term
  | App of term * term list
  | PrimApp of operator * term list

  val substRegVar : (RegionSet.regionvar * RegionSet.regionvar) -> term -> term
  val substRegVarValue : (RegionSet.regionvar * RegionSet.regionvar) -> value -> value
end
=
struct
  type var = string
  type operator = string
  datatype value =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  | Lambda of RegionSet.regionset * (var * Ty.ty) list * Ty.ty * RegionSet.effect * term
  | Tuple of term list
  and term = 
    Value of value
  | Var of var
  | Select of int * term
  | Box of term * RegionSet.regionvar
  | Unbox of term
  | Let of var * term * term * Ty.ty
  | LetRegion of RegionSet.regionvar * term
  | RegionElim of RegionSet.regionset * term
  | IfElse of term * term * term
  | App of term * term list
  | PrimApp of operator * term list

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
      RegionElim (Set.map (fn r => if dst = r then newr else r) rs, substRegVar (dst, newr) m)
  | substRegVar (dst, newr) (App (m1, m2)) = 
      App (substRegVar (dst, newr) m1, map (substRegVar (dst, newr)) m2)
  | substRegVar (dst, newr) (PrimApp (opr, m)) = 
      PrimApp (opr, map (substRegVar (dst, newr)) m)

  and substRegVarValue (dst, newr) (IntLit i) = IntLit i
  | substRegVarValue (dst, newr) (BoolLit b) = BoolLit b
  | substRegVarValue (dst, newr) (UnitLit) = UnitLit
  | substRegVarValue (dst, newr) (Lambda (rs, args, rt, phi, m)) = 
      Lambda (rs, map (fn (x, t) => (x, Ty.substRegVarTy (dst, newr) t)) args,
        Ty.substRegVarTy (dst, newr) rt,
        Set.map (fn r => if dst = r then newr else r) phi,
        substRegVar (dst, newr) m)
  | substRegVarValue (dst, newr) (Tuple m) = 
      Tuple (map (substRegVar (dst, newr)) m)
end

