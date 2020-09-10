structure FirstOrderTerm :
sig
  datatype var =
    NamedVar of string
  | GenVar of int
  | IndexVar of int
  type operator = string
  datatype value =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  | CodePtr of var
  | Tuple of atom list
  and atom =
    Value of value
  | Var of var
  and comp =
    Atom of atom
  | Select of int * atom
  | Box of atom * RegionSet.regionvar
  | Unbox of atom
  | RegionElim of RegionSet.regionset * atom
  | App of atom * atom list
  | PrimApp of operator * atom list
  and term =
    AtomTerm of atom
  | Let of var * comp * term
  | LetRegion of RegionSet.regionvar * term
  | IfElse of atom * term * term

  val substRegVarValue : (RegionSet.regionvar * RegionSet.regionvar) -> value -> value
  val substRegVarAtom : (RegionSet.regionvar * RegionSet.regionvar) -> atom -> atom
  val substRegVarComp : (RegionSet.regionvar * RegionSet.regionvar) -> comp -> comp
  val substRegVar : (RegionSet.regionvar * RegionSet.regionvar) -> term -> term
end
=
struct
  datatype var =
    NamedVar of string
  | GenVar of int
  | IndexVar of int
  type operator = string
  datatype value =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  | CodePtr of var
  | Tuple of atom list
  and atom =
    Value of value
  | Var of var
  and comp =
    Atom of atom
  | Select of int * atom
  | Box of atom * RegionSet.regionvar
  | Unbox of atom
  | RegionElim of RegionSet.regionset * atom
  | App of atom * atom list
  | PrimApp of operator * atom list
  and term =
    AtomTerm of atom
  | Let of var * comp * term
  | LetRegion of RegionSet.regionvar * term
  | IfElse of atom * term * term

  fun substRegVarValue (dst, newr) (IntLit i) = IntLit i
  | substRegVarValue (dst, newr) (BoolLit b) = BoolLit b
  | substRegVarValue (dst, newr) (UnitLit) = UnitLit
  | substRegVarValue (dst, newr) (CodePtr p) = CodePtr p
  | substRegVarValue (dst, newr) (Tuple m) = 
      Tuple (map (substRegVarAtom (dst, newr)) m)

  and substRegVarAtom (dst, newr) (Value v) = Value (substRegVarValue (dst, newr) v)
  | substRegVarAtom (dst, newr) (Var v) = Var v

  and substRegVarComp (dst, newr) (Atom (m)) =
      Atom (substRegVarAtom (dst, newr) m)
  | substRegVarComp (dst, newr) (Select (i, m)) =
      Select (i, substRegVarAtom (dst, newr) m)
  | substRegVarComp (dst, newr) (Box (m, r)) = 
      Box (substRegVarAtom (dst, newr) m, if dst = r then newr else r)
  | substRegVarComp (dst, newr) (Unbox m) = 
      Unbox (substRegVarAtom (dst, newr) m)
  | substRegVarComp (dst, newr) (RegionElim (rs, m)) = 
      RegionElim (Set.map (fn r => if dst = r then newr else r) rs, substRegVarAtom (dst, newr) m)
  | substRegVarComp (dst, newr) (App (m1, m2)) = 
      App (substRegVarAtom (dst, newr) m1, map (substRegVarAtom (dst, newr)) m2)
  | substRegVarComp (dst, newr) (PrimApp (opr, m)) = 
      PrimApp (opr, map (substRegVarAtom (dst, newr)) m)

  and substRegVar (dst, newr) (AtomTerm (m)) =
      AtomTerm (substRegVarAtom (dst, newr) m)
  | substRegVar (dst, newr) (Let (x, m1, m2)) = 
      Let (x, substRegVarComp (dst, newr) m1, substRegVar (dst, newr) m2)
  | substRegVar (dst, newr) (LetRegion (r, m)) = 
      LetRegion (r, substRegVar (dst, newr) m)
  | substRegVar (dst, newr) (IfElse (m1, m2, m3)) = 
      IfElse (substRegVarAtom (dst, newr) m1,
        substRegVar (dst, newr) m2,
        substRegVar (dst, newr) m3)

end

