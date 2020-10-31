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
  datatype pattern =
    PatLit of lit
  | PatVar of name
  | PatTuple of pattern * pattern
  | PatCons of name * pattern list
  datatype path =
    PVar of var
  | PPath of modexpr * var
  and term =
    Path of path
  | Lit of lit
  | Sort of sort
  | App of term * term
  | Case of term * (pattern * term) list * term
  | IfElse of term * term * term
  | Let of var * term * term * term
  | Lambda of var * term * term
  | DepProduct of var * term * term
  and def =
    DefVal of term
  | DefData of term * (name * term) list
  | DefMod of modexpr
  | DefModSig of modexpr * modtype
  | DefModTransparent of modexpr
  and modtype =
    ModTypeSig of (var * specification) list
  | ModTypeFunctor of var * modtype * modtype
  and specification =
    SpecAbsMod of modtype
  | SpecManifestMod of modtype * modexpr
  | SpecAbsTerm of term
  | SpecManifestTerm of term * term
  and modexpr =
    ModStruct of (var * def) list
  | ModFunctor of var * modtype * modexpr
  | ModApp of modexpr * modexpr
  | ModPath of path
  and toplvl =
    TopSpec of specification
  | TopDef of def
  type program = (var * toplvl) list

  val subst : var -> term -> term -> term
  val substDef : var -> term -> def -> def
  val substSpec : var -> term -> specification -> specification
  val substModtype : var -> term -> modtype -> modtype
  val substModexpr : var -> term -> modexpr -> modexpr
  val eqv : var -> var -> bool
  val eq : term -> term -> bool

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
  datatype pattern =
    PatLit of lit
  | PatVar of name
  | PatTuple of pattern * pattern
  | PatCons of name * pattern list
  datatype path =
    PVar of var
  | PPath of modexpr * var
  and term =
    Path of path
  | Lit of lit
  | Sort of sort
  | App of term * term
  | Case of term * (pattern * term) list * term
  | IfElse of term * term * term
  | Let of var * term * term * term
  | Lambda of var * term * term
  | DepProduct of var * term * term
  and def =
    DefVal of term
  | DefData of term * (name * term) list
  | DefMod of modexpr
  | DefModSig of modexpr * modtype
  | DefModTransparent of modexpr
  and modtype =
    ModTypeSig of (var * specification) list
  | ModTypeFunctor of var * modtype * modtype
  and specification =
    SpecAbsMod of modtype
  | SpecManifestMod of modtype * modexpr
  | SpecAbsTerm of term
  | SpecManifestTerm of term * term
  and modexpr =
    ModStruct of (var * def) list
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

  fun subst x x' (Path (PVar v)) =
    if eqv x v then x' else Path (PVar v)
  | subst x x' (Path p) = Path p
  | subst x x' (Lit l) = Lit l
  | subst x x' (Sort s) = Sort s
  | subst x x' (App (m1, m2)) =
      App (subst x x' m1, subst x x' m2)
  | subst x x' (Case (m1, pml, m2)) = raise Fail ""
  | subst x x' (IfElse (m1, m2, m3)) =
      IfElse (subst x x' m1, subst x x' m2, subst x x' m3)
  | subst x x' (Let (v, m1, m2, m3)) =
      Let (v, subst x x' m1, subst x x' m2, subst x x' m3)
  | subst x x' (Lambda (v, m1, m2)) =
      Lambda (v, subst x x' m1, subst x x' m2)
  | subst x x' (DepProduct (v, m1, m2)) =
      DepProduct (v, subst x x' m1, subst x x' m2)
  and substDef x x' (DefVal m) = DefVal (subst x x' m)
  | substDef x x' (DefData (m, nml)) =
      DefData (subst x x' m, map (fn (n, m') => (n, subst x x' m')) nml)
  | substDef x x' (DefMod m) = DefMod (substModexpr x x' m)
  | substDef x x' (DefModSig (m1, m2)) =
      DefModSig (substModexpr x x' m1, substModtype x x' m2)
  | substDef x x' (DefModTransparent m) = DefModTransparent (substModexpr x x' m)
  and substSpec x x' (SpecAbsMod m) = SpecAbsMod (substModtype x x' m)
  | substSpec x x' (SpecManifestMod (m1, m2)) =
      SpecManifestMod (substModtype x x' m1, substModexpr x x' m2)
  | substSpec x x' (SpecAbsTerm m) = SpecAbsTerm (subst x x' m)
  | substSpec x x' (SpecManifestTerm (m1, m2)) =
      SpecManifestTerm (subst x x' m1, subst x x' m2)
  and substModtype x x' (ModTypeSig sl) =
      ModTypeSig (map (fn (v, s) => (v, substSpec x x' s)) sl)
  | substModtype x x' (ModTypeFunctor (v, m1, m2)) =
      ModTypeFunctor (v, substModtype x x' m1, substModtype x x' m2)
  and substModexpr x x' (ModStruct ml) =
      ModStruct (map (fn (v, d) => (v, substDef x x' d)) ml)
  | substModexpr x x' (ModFunctor (v, m1, m2)) =
      ModFunctor (v, substModtype x x' m1, substModexpr x x' m2)
  | substModexpr x x' (ModApp (m1, m2)) =
      ModApp (substModexpr x x' m1, substModexpr x x' m2)
  | substModexpr x x' (ModPath p) = ModPath p

  fun eq (Path p) (Path p') = p = p'
  | eq (Lit l) (Lit l') = l = l'
  | eq (Sort s) (Sort s') = s = s'
  | eq (App (m1, m2)) (App (m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (Case (m1, pml, m2)) (Case (m1', pml', m2')) =
      raise Fail ""
  | eq (IfElse (m1, m2, m3)) (IfElse (m1', m2', m3')) =
      eq m1 m1' andalso eq m2 m2' andalso eq m3 m3'
  | eq (Let (AnonVar, m1, m2, m3)) (Let (v', m1', m2', m3')) =
      eq m1 m1' andalso eq m2 m2' andalso eq m3 m3'
  | eq (Let (v, m1, m2, m3)) (Let (AnonVar, m1', m2', m3')) =
      eq m1 m1' andalso eq m2 m2' andalso eq m3 m3'
  | eq (Let (v, m1, m2, m3)) (Let (v', m1', m2', m3')) =
      if eqv v v' then eq m1 m1' andalso eq m2 m2' andalso eq m3 m3'
      else eq m1 m1' andalso eq m2 m2'
        andalso eq m3 (subst v' (Path (PVar v)) m3')
  | eq (Lambda (AnonVar, m1, m2)) (Lambda (_, m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (Lambda (_, m1, m2)) (Lambda (AnonVar, m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (Lambda (v, m1, m2)) (Lambda (v', m1', m2')) =
      if eqv v v' then eq m1 m1' andalso eq m2 m2'
      else eq m1 m1' andalso eq m2 (subst v' (Path (PVar v)) m2')
  | eq (DepProduct (AnonVar, m1, m2)) (DepProduct (_, m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (DepProduct (_, m1, m2)) (DepProduct (AnonVar, m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (DepProduct (v, m1, m2)) (DepProduct (v', m1', m2')) =
      if eqv v v' then eq m1 m1' andalso eq m2 m2'
      else eq m1 m1' andalso eq m2 (subst v' (Path (PVar v)) m2')
  | eq _ _ = false

end

