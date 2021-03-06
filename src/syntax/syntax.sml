structure Syntax = struct
  type name = string
  type var = MTS.var
  type sort = MTS.sort
  type lit = MTS.lit
  type path = var list
  datatype term =
    Path of path
  | Lit of lit
  | Sort of sort
  | App of term * term list
  | Case of term * term * (path * var list * term) list
  | IfElse of term * term * term
  | Let of var * term * term * term
  | Lambda of (var * term) list * term
  | DepProduct of (var * term) list * term
  and def =
    DefTerm of var * term
  | DefTermTyped of var * term * term
  | DefMod of var * modexpr
  | DefModSig of var * modexpr * modtype
  | DefModTransparent of var * modexpr
  | DefInductive of var * term * (var * term) list
  | DefFixpoint of var * term * term
  and modtype =
    ModTypeSig of specification list
  | ModTypeFunctor of (var * modtype) list * modtype
  and specification =
    SpecAbsMod of var * modtype
  | SpecManifestMod of var * modtype * modexpr
  | SpecAbsTerm of var * term
  | SpecManifestTerm of var * term * term
  | SpecInductive of var * term * (var * term) list
  and modexpr =
    ModStruct of def list
  | ModFunctor of var * modtype * modexpr
  | ModApp of modexpr * modexpr
  | ModPath of path
  type program = def list
end
