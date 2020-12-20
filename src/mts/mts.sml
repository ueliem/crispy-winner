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
  | Case of term * term * (term) list
  | IfElse of term * term * term
  | Let of var * term * term * term
  | Lambda of var * term * term
  | DepProduct of var * term * term
  | Inductive of (var * term) * term list
  | Constr of int * term
  and def =
    DefVal of term
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

  val eqv : var -> var -> bool
  val eqvs : var list -> var list -> bool
  val fvTerm : term -> var Set.set
  val fvModexpr : modexpr -> var Set.set
  val fvModtype : modtype -> var Set.set
  val fvSpec : specification -> var Set.set
  val fvDef : def -> var Set.set
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
  | Case of term * term * (term) list
  | IfElse of term * term * term
  | Let of var * term * term * term
  | Lambda of var * term * term
  | DepProduct of var * term * term
  | Inductive of (var * term) * term list
  | Constr of int * term
  and def =
    DefVal of term
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

  fun eqvs vs vs' =
    let fun f ([]) = true
    | f ((x, x')::xs) = eqv x x' andalso f xs
    in f (ListPair.zipEq (vs, vs')) end

  fun fvTerm (Path (PVar v)) = Set.singleton v
    | fvTerm (Path (PPath (p, v))) = fvModexpr p
    | fvTerm (Lit _) = Set.emptyset
    | fvTerm (Sort _) = Set.emptyset
    | fvTerm (App (t1, t2)) = Set.union (fvTerm t1) (fvTerm t2)
    (* | fvTerm (Case (t, alts)) = v * vl * t *)
    | fvTerm (IfElse (t1, t2, t3)) =
        Set.union (Set.union (fvTerm t1) (fvTerm t2)) (fvTerm t3)
    | fvTerm (Let (v, t1, t2, t3)) =
        Set.remove v
          (Set.union (Set.union (fvTerm t1) (fvTerm t2)) (fvTerm t3))
    | fvTerm (Lambda (v, t1, t2)) =
        Set.remove v (Set.union (fvTerm t1) (fvTerm t2))
    | fvTerm (DepProduct (v, t1, t2)) =
        Set.remove v (Set.union (fvTerm t1) (fvTerm t2))
    | fvTerm (Inductive ((v, t1), tl)) =
        Set.union (fvTerm t1) (foldl (fn (t', s) =>
          Set.union s (fvTerm t')) Set.emptyset tl)
    | fvTerm (Constr (i, t)) = fvTerm t
  and fvModexpr (ModStruct dl) =
    let fun f ([]) = Set.emptyset
      | f ((v, d)::dl') =
        Set.remove v (Set.union (f dl') (fvDef d))
    in f dl end
    | fvModexpr (ModFunctor (v, m1, m2)) =
      Set.remove v (Set.union (fvModtype m1) (fvModexpr m2))
    | fvModexpr (ModApp (m1, m2)) =
      Set.union (fvModexpr m1) (fvModexpr m2)
    | fvModexpr (ModPath (PVar v)) = Set.singleton v
    | fvModexpr (ModPath (PPath (p, v))) = fvModexpr p
  and fvModtype (ModTypeSig sl) =
    let fun f ([]) = Set.emptyset
      | f ((v, s)::sl') =
        Set.remove v (Set.union (f sl') (fvSpec s))
    in f sl end
    | fvModtype (ModTypeFunctor (v, m1, m2)) =
      Set.remove v (Set.union (fvModtype m1) (fvModtype m2))
  and fvSpec (SpecAbsMod m) = fvModtype m
  | fvSpec (SpecManifestMod (m1, m2)) = Set.union (fvModtype m1) (fvModexpr m2)
  | fvSpec (SpecAbsTerm t) = fvTerm t
  | fvSpec (SpecManifestTerm (t1, t2)) = Set.union (fvTerm t1) (fvTerm t2)
  and fvDef (DefVal t) = fvTerm t
  | fvDef (DefMod m) = fvModexpr m
  | fvDef (DefModSig (m1, m2)) = Set.union (fvModexpr m1) (fvModtype m2)
  | fvDef (DefModTransparent m) = fvModexpr m
end

