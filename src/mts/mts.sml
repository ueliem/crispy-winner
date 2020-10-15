structure MTS :
sig
  type name = string
  datatype var =
    NamedVar of name
  | GenVar of int
  | IndexVar of int * name
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

  val eqv : var -> var -> bool
  val eq : term -> term -> bool

end
=
struct
  type name = string
  datatype var =
    NamedVar of name
  | GenVar of int
  | IndexVar of int * name
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

  fun eqv (NamedVar n) (NamedVar n') = n = n'
  | eqv (IndexVar (i, _)) (IndexVar (i', _)) = i = i'
  | eqv _ _ = raise Fail "gotta think on this"

  fun eq (Var v) (Var v') = eqv v v'
  | eq (Lit l) (Lit l') = l = l'
  | eq (Sort s) (Sort s') = s = s'
  | eq (App (m1, m2)) (App (m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (IfElse (m1, m2, m3)) (IfElse (m1', m2', m3')) =
      eq m1 m1' andalso eq m2 m2' andalso eq m3 m3'
  | eq (Let (v, m1, m2, m3)) (Let (v', m1', m2', m3')) =
      eqv v v' andalso eq m1 m1' andalso eq m2 m2'
  | eq (Lambda (v, m1, m2)) (Lambda (v', m1', m2')) =
      eqv v v' andalso eq m1 m1' andalso eq m2 m2'
  | eq (DepProduct (v, m1, m2)) (DepProduct (v', m1', m2')) =
      eqv v v' andalso eq m1 m1' andalso eq m2 m2'
  | eq _ _ = false

end

