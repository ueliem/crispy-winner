structure MTS :
sig
  type name = string
  datatype var =
    NamedVar of name
  | GenVar of int
  | AnonVar
  datatype sort =
    TypeVal
  | KindVal
  | TypeComp
  | KindComp
  type sorts = sort list
  type ax = (sort * sort) list
  type rules = (sort * sort * sort) list
  datatype lit =
    IntLit of int
  | BoolLit of bool
  | IntTyLit
  | BoolTyLit
  datatype path =
    PVar of var
  | PPath of modexpr * var
  and term =
    Path of path
  | Lit of lit
  | Sort of sort
  | App of term * term
  | Case of term * (var * var list * term) list
  | IfElse of term * term * term
  | Let of var * term * term * term
  | Lambda of var * term * term
  | DepProduct of var * term * term
  and def =
    DefVal of term
  | DefData of term * ((var * var) * term) list
  | DefMod of modexpr
  | DefModSig of modexpr * modtype
  | DefModTransparent of modexpr
  and modtype =
    ModTypeSig of ((var * var) * specification) list
  | ModTypeFunctor of var * modtype * modtype
  and specification =
    SpecAbsMod of modtype
  | SpecManifestMod of modtype * modexpr
  | SpecAbsTerm of term
  | SpecManifestTerm of term * term
  and modexpr =
    ModStruct of ((var * var) * def) list
  | ModFunctor of var * modtype * modexpr
  | ModApp of modexpr * modexpr
  | ModPath of path
  and toplvl =
    TopSpec of specification
  | TopDef of def
  type program = (var * toplvl) list

  val subst : var -> term -> term -> term

  val eqv : var -> var -> bool
  val eqvs : var list -> var list -> bool
end
=
struct
  type name = string
  datatype var =
    NamedVar of name
  | GenVar of int
  | AnonVar
  datatype sort =
    TypeVal
  | KindVal
  | TypeComp
  | KindComp
  type sorts = sort list
  type ax = (sort * sort) list
  type rules = (sort * sort * sort) list
  datatype lit =
    IntLit of int
  | BoolLit of bool
  | IntTyLit
  | BoolTyLit
  datatype path =
    PVar of var
  | PPath of modexpr * var
  and term =
    Path of path
  | Lit of lit
  | Sort of sort
  | App of term * term
  | Case of term * (var * var list * term) list
  | IfElse of term * term * term
  | Let of var * term * term * term
  | Lambda of var * term * term
  | DepProduct of var * term * term
  and def =
    DefVal of term
  | DefData of term * ((var * var) * term) list
  | DefMod of modexpr
  | DefModSig of modexpr * modtype
  | DefModTransparent of modexpr
  and modtype =
    ModTypeSig of ((var * var) * specification) list
  | ModTypeFunctor of var * modtype * modtype
  and specification =
    SpecAbsMod of modtype
  | SpecManifestMod of modtype * modexpr
  | SpecAbsTerm of term
  | SpecManifestTerm of term * term
  and modexpr =
    ModStruct of ((var * var) * def) list
  | ModFunctor of var * modtype * modexpr
  | ModApp of modexpr * modexpr
  | ModPath of path
  and toplvl =
    TopSpec of specification
  | TopDef of def
  type program = (var * toplvl) list

  fun eqv (NamedVar n) (NamedVar n') = (n = n')
  | eqv (GenVar n) (GenVar n') = (n = n')
  | eqv _ _ = false

  fun eqvs vs vs' =
    let fun f ([]) = true
    | f ((x, x')::xs) = eqv x x' andalso f xs
    in f (ListPair.zipEq (vs, vs')) end

  fun subst x x' (Path (PVar v)) =
    if eqv x v then x' else Path (PVar v)
  | subst x x' (Path p) = Path p
  | subst x x' (Lit l) = Lit l
  | subst x x' (Sort s) = Sort s
  | subst x x' (App (m1, m2)) =
      App (subst x x' m1, subst x x' m2)
  | subst x x' (Case (m, pml)) =
      Case (subst x x' m, map (fn (c, vs, m') =>
        (c, vs, subst x x' m')) pml)
  | subst x x' (IfElse (m1, m2, m3)) =
      IfElse (subst x x' m1, subst x x' m2, subst x x' m3)
  | subst x x' (Let (v, m1, m2, m3)) =
      if eqv x v then (Let (v, m1, m2, m3)) 
      else Let (v, subst x x' m1, subst x x' m2, subst x x' m3)
  | subst x x' (Lambda (v, m1, m2)) =
      if eqv x v then (Lambda (v, m1, m2))
      else Lambda (v, subst x x' m1, subst x x' m2)
  | subst x x' (DepProduct (v, m1, m2)) =
      if eqv x v then (DepProduct (v, m1, m2))
      else DepProduct (v, subst x x' m1, subst x x' m2)

end

