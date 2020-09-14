structure ANFTerm :
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
  | Lambda of RegionSet.regionset * var list * term
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

  val freevarsTerm : var list -> term -> var Set.set

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
  | Lambda of RegionSet.regionset * var list * term
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

  fun isfreevar bv v =
    if (List.exists (fn x => x = v) bv) then Set.emptyset else Set.singleton v

  fun freevarsValue bv (IntLit _) = Set.emptyset
  | freevarsValue bv (BoolLit _) = Set.emptyset
  | freevarsValue bv (UnitLit) = Set.emptyset
  | freevarsValue bv (Lambda (rs, vl, m)) =
      freevarsTerm (vl @ bv) m
  | freevarsValue bv (Tuple m) =
      foldl (fn (v, s) => Set.union s (isfreevar bv v)) Set.emptyset m

  and freevarsComp bv (Value v) = freevarsValue bv v
  | freevarsComp bv (Var v) = isfreevar bv v
  | freevarsComp bv (Select (i, m)) = isfreevar bv m
  | freevarsComp bv (Box (m, r)) = isfreevar bv m
  | freevarsComp bv (Unbox m) = isfreevar bv m
  | freevarsComp bv (RegionElim (rs, m)) = isfreevar bv m
  | freevarsComp bv (App (m1, m2)) =
      foldl (fn (v, s) => Set.union s (isfreevar bv v)) (isfreevar bv m1) m2
  | freevarsComp bv (PrimApp (opr, m)) =
      foldl (fn (v, s) => Set.union s (isfreevar bv v)) Set.emptyset m

  and freevarsTerm bv (Return x) = isfreevar bv x
  | freevarsTerm bv (Let (x, m1, m2)) =
      Set.union (freevarsComp (x::bv) m1) (freevarsTerm (x::bv) m2)
  | freevarsTerm bv (LetRegion (r, m)) =
      freevarsTerm bv m
  | freevarsTerm bv (IfElse (m1, m2, m3)) =
      Set.union (isfreevar bv m1) 
        (Set.union (freevarsTerm bv m2) (freevarsTerm bv m3))

end

