structure CoreFromSyntax = struct
  open Syntax
  fun fromPath p =
    foldl (fn (v, m) => MTS.PPath (MTS.ModPath m, v))
      (MTS.PVar (hd p)) (tl p)
  (* and fromTerm (Path of path
  | Lit of lit
  | Sort of sort
  | App of term * term
  | Case of term * term * (path * var list * term) list
  | IfElse of term * term * term
  | Let of var * term * term * term
  | Lambda of (var * term) list * term
  | DepProduct of (var * term) list * term
  and fromDef (DefTerm (v, t)) =
  | fromDef (DefTermTyped (v, t1, t2)) =
  | fromDef (DefMod (v, m)) =
  | fromDef (DefModSig (v, m1, m2)) =
  | fromDef (DefModTransparent (v, m)) =
  | fromDef (DefInductive (v, t, vtl)) =
  and fromModtype =
    ModTypeSig of specification list
  | ModTypeFunctor of (var * modtype) list * modtype
  and fromSpecification =
    SpecAbsMod of var * modtype
  | SpecManifestMod of var * modtype * modexpr
  | SpecAbsTerm of var * term
  | SpecManifestTerm of var * term * term
  | SpecInductive of var * term * (var * term) list
  and fromModexpr =
    ModStruct of def list
  | ModFunctor of var * modtype * modexpr
  | ModApp of modexpr * modexpr
  | ModPath of path
  *)
  (* and toplvl =
    TopSpec of specification
  | TopDef of def
  type program = (var * toplvl) list
  *)
end
