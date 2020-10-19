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
  datatype modpath =
    PathVar of name
  | PathMod of modpath * name
  datatype term =
    Var of var
  | Path of modpath
  | Lit of lit
  | Sort of sort
  | App of term * term
  | Case of term * (pattern * term) list * term
  | IfElse of term * term * term
  | Let of var * term * term * term
  | Lambda of var * term * term
  | DepProduct of var * term * term
  type datadef = name * term * (name * term) list
  datatype def =
    DefVal of var * term * term
  | DefData of datadef
  | DefMod of name * modexpr
  | DefModSig of name * modexpr * modtype
  | DefModTransparent of name * modexpr
  and modtype =
    ModTypeSig of specification list
  | ModTypeFunctor of var * modtype * modtype
  and specification =
    SpecAbsMod of modtype
  | SpecManifestMod of modtype * modexpr
  | SpecAbsTerm of term
  | SpecManifestTerm of term * term
  and modexpr =
    ModStruct of def list
  | ModFunctor of var * modtype * modexpr
  | ModApp of modexpr * modexpr
  | ModPath of modpath
  and toplvl =
    TopSpec of specification
  | TopDef of def
  type program = (var * toplvl) list

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
  datatype modpath =
    PathVar of name
  | PathMod of modpath * name
  datatype term =
    Var of var
  | Path of modpath
  | Lit of lit
  | Sort of sort
  | App of term * term
  | Case of term * (pattern * term) list * term
  | IfElse of term * term * term
  | Let of var * term * term * term
  | Lambda of var * term * term
  | DepProduct of var * term * term
  type datadef = name * term * (name * term) list
  datatype def =
    DefVal of var * term * term
  | DefData of datadef
  | DefMod of name * modexpr
  | DefModSig of name * modexpr * modtype
  | DefModTransparent of name * modexpr
  and modtype =
    ModTypeSig of specification list
  | ModTypeFunctor of var * modtype * modtype
  and specification =
    SpecAbsMod of modtype
  | SpecManifestMod of modtype * modexpr
  | SpecAbsTerm of term
  | SpecManifestTerm of term * term
  and modexpr =
    ModStruct of def list
  | ModFunctor of var * modtype * modexpr
  | ModApp of modexpr * modexpr
  | ModPath of modpath
  and toplvl =
    TopSpec of specification
  | TopDef of def
  type program = (var * toplvl) list

  fun eqv (NamedVar n) (NamedVar n') = n = n'
  fun eqv (GenVar n) (GenVar n') = n = n'
  | eqv _ _ = false

  fun subst x x' (Var v) =
      if eqv v x then x' else Var v
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

  fun eq (Var v) (Var v') = eqv v v'
  | eq (Path p) (Path p') = p = p'
  | eq (Lit l) (Lit l') = l = l'
  | eq (Sort s) (Sort s') = s = s'
  | eq (App (m1, m2)) (App (m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (Case (m1, pml, m2)) (Case (m1', pml', m2')) =
      raise Fail ""
  | eq (IfElse (m1, m2, m3)) (IfElse (m1', m2', m3')) =
      eq m1 m1' andalso eq m2 m2' andalso eq m3 m3'

  | eq (Let (v, m1, m2, m3)) (Let (v', m1', m2', m3')) =
      eqv v v'
        andalso eq m1 m1'
        andalso eq m2 m2'
        andalso eq m3 m3'

  | eq (Lambda (AnonVar, m1, m2)) (Lambda (_, m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (Lambda (_, m1, m2)) (Lambda (AnonVar, m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (Lambda (v, m1, m2)) (Lambda (v', m1', m2')) =
      if eqv v v' then eq m1 m1' andalso eq m2 m2'
      else raise Fail ""

  | eq (DepProduct (AnonVar, m1, m2)) (DepProduct (_, m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (DepProduct (_, m1, m2)) (DepProduct (AnonVar, m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (DepProduct (v, m1, m2)) (DepProduct (v', m1', m2')) =
      if eqv v v' then eq m1 m1' andalso eq m2 m2'
      else raise Fail ""

  | eq _ _ = false

end

