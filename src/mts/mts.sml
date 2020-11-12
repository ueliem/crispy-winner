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
  structure VSub : sig
    val substDef : var -> var -> def -> def
    val substSpec : var -> var -> specification -> specification
    val substModtype : var -> var -> modtype -> modtype
    val substModexpr : var -> var -> modexpr -> modexpr
  end
  structure MSub : sig
    val substDef : var -> modexpr -> def -> def
    val substSpec : var -> modexpr -> specification -> specification
    val substModtype : var -> modexpr -> modtype -> modtype
    val substModexpr : var -> modexpr -> modexpr -> modexpr
  end
  structure PSub : sig
    val substDef : var -> path -> def -> def
    val substSpec : var -> path -> specification -> specification
    val substModtype : var -> path -> modtype -> modtype
    val substModexpr : var -> path -> modexpr -> modexpr
  end

  val eqv : var -> var -> bool
  val eq : term -> term -> bool
  val mexpreq : modexpr -> modexpr -> bool
  val mtypeeq : modtype -> modtype -> bool
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

  structure VSub = struct
    fun substTerm x x' (Path (PVar v)) =
      if eqv x v then Path (PVar x') else Path (PVar v)
    | substTerm x x' (Path (PPath (p, v))) =
        Path (PPath (substModexpr x x' p, v))
    | substTerm x x' (Lit l) = Lit l
    | substTerm x x' (Sort s) = Sort s
    | substTerm x x' (App (m1, m2)) =
        App (substTerm x x' m1, substTerm x x' m2)
    | substTerm x x' (Case (m1, pml, m2)) = raise Fail ""
    | substTerm x x' (IfElse (m1, m2, m3)) =
        IfElse (substTerm x x' m1, substTerm x x' m2, substTerm x x' m3)
    | substTerm x x' (Let (v, m1, m2, m3)) =
        if eqv x v then Let (v, m1, m2, m3)
        else Let (v, substTerm x x' m1, substTerm x x' m2, substTerm x x' m3)
    | substTerm x x' (Lambda (v, m1, m2)) =
        if eqv x v then Lambda (v, m1, m2)
        else Lambda (v, substTerm x x' m1, substTerm x x' m2)
    | substTerm x x' (DepProduct (v, m1, m2)) =
        if eqv x v then DepProduct (v, m1, m2)
        else DepProduct (v, substTerm x x' m1, substTerm x x' m2)
    and substDef x x' (DefVal m) = DefVal (substTerm x x' m)
    | substDef x x' (DefData (m, nml)) = raise Fail ""
        (* DefData (substTerm x x' m, map (fn (n, m') => (n, substTerm x x' m')) nml) *)
    | substDef x x' (DefMod m) = DefMod (substModexpr x x' m)
    | substDef x x' (DefModSig (m1, m2)) =
        DefModSig (substModexpr x x' m1, substModtype x x' m2)
    | substDef x x' (DefModTransparent m) = DefModTransparent (substModexpr x x' m)
    and substSpec x x' (SpecAbsMod m) = SpecAbsMod (substModtype x x' m)
    | substSpec x x' (SpecManifestMod (m1, m2)) =
        SpecManifestMod (substModtype x x' m1,
        substModexpr x x' m2)
    | substSpec x x' (SpecAbsTerm m) = SpecAbsTerm (substTerm x x' m)
    | substSpec x x' (SpecManifestTerm (m1, m2)) =
        SpecManifestTerm (substTerm x x' m1, substTerm x x' m2)
    and substModtype x x' (ModTypeSig sl) =
      let fun f sl'' ([]) = sl''
        | f sl'' (((v1, v2), s)::sl') =
            if eqv x v2 then
              (List.rev sl'') @ (((v1, v2), s)::sl')
            else
              f (((v1, v2), substSpec x x' s)::sl'') sl'
        in ModTypeSig (f [] sl) end
    | substModtype x x' (ModTypeFunctor (v, m1, m2)) =
        if eqv x v then (ModTypeFunctor (v, m1, m2))
        else ModTypeFunctor (v, substModtype x x' m1, substModtype x x' m2)
    and substModexpr x x' (ModStruct ml) =
      let fun f ml'' ([]) = ml''
        | f ml'' (((v1, v2), d)::ml') =
            if eqv x v2 then
              (List.rev ml'') @ (((v1, v2), d)::ml')
            else
              f (((v1, v2), substDef x x' d)::ml'') ml'
        in ModStruct (f [] ml) end
    | substModexpr x x' (ModFunctor (v, m1, m2)) =
        if eqv x v then (ModFunctor (v, m1, m2))
        else ModFunctor (v, substModtype x x' m1, substModexpr x x' m2)
    | substModexpr x x' (ModApp (m1, m2)) =
        ModApp (substModexpr x x' m1, substModexpr x x' m2)
    | substModexpr x x' (ModPath (PPath (m, v))) =
        ModPath (PPath (substModexpr x x' m, v))
    | substModexpr x x' (ModPath (PVar v)) =
        if x = v then ModPath (PVar x') else ModPath (PVar v)
  end
  structure MSub = struct
    fun substTerm x x' (Path (PVar v)) = Path (PVar v)
    | substTerm x x' (Path (PPath (p, v))) =
        Path (PPath (substModexpr x x' p, v))
    | substTerm x x' (Lit l) = Lit l
    | substTerm x x' (Sort s) = Sort s
    | substTerm x x' (App (m1, m2)) =
        App (substTerm x x' m1, substTerm x x' m2)
    | substTerm x x' (Case (m1, pml, m2)) = raise Fail ""
    | substTerm x x' (IfElse (m1, m2, m3)) =
        IfElse (substTerm x x' m1, substTerm x x' m2, substTerm x x' m3)
    | substTerm x x' (Let (v, m1, m2, m3)) =
        Let (v, substTerm x x' m1, substTerm x x' m2, substTerm x x' m3)
    | substTerm x x' (Lambda (v, m1, m2)) =
        Lambda (v, substTerm x x' m1, substTerm x x' m2)
    | substTerm x x' (DepProduct (v, m1, m2)) =
        DepProduct (v, substTerm x x' m1, substTerm x x' m2)
    and substDef x x' (DefVal m) = DefVal (substTerm x x' m)
    | substDef x x' (DefData (m, nml)) =
        DefData (substTerm x x' m, map (fn (n, m') => (n, substTerm x x' m')) nml)
    | substDef x x' (DefMod m) = DefMod (substModexpr x x' m)
    | substDef x x' (DefModSig (m1, m2)) =
        DefModSig (substModexpr x x' m1, substModtype x x' m2)
    | substDef x x' (DefModTransparent m) = DefModTransparent (substModexpr x x' m)
    and substSpec x x' (SpecAbsMod m) = SpecAbsMod (substModtype x x' m)
    | substSpec x x' (SpecManifestMod (m1, m2)) =
        SpecManifestMod (substModtype x x' m1,
        substModexpr x x' m2)
    | substSpec x x' (SpecAbsTerm m) = SpecAbsTerm (substTerm x x' m)
    | substSpec x x' (SpecManifestTerm (m1, m2)) =
        SpecManifestTerm (substTerm x x' m1, substTerm x x' m2)
    and substModtype x x' (ModTypeSig sl) =
        ModTypeSig (map (fn ((v1, v2), s) => ((v1, v2), substSpec x x' s)) sl)
    | substModtype x x' (ModTypeFunctor (v, m1, m2)) =
        ModTypeFunctor (v, substModtype x x' m1, substModtype x x' m2)
    and substModexpr x x' (ModStruct ml) =
        ModStruct (map (fn ((v1, v2), d) => ((v1, v2), substDef x x' d)) ml)
    | substModexpr x x' (ModFunctor (v, m1, m2)) =
        ModFunctor (v, substModtype x x' m1, substModexpr x x' m2)
    | substModexpr x x' (ModApp (m1, m2)) =
        ModApp (substModexpr x x' m1, substModexpr x x' m2)
    | substModexpr x x' (ModPath (PPath (m, v))) =
        ModPath (PPath (substModexpr x x' m, v))
    | substModexpr x x' (ModPath (PVar v)) =
        if x = v then x' else ModPath (PVar v)
  end
  structure PSub = struct
    fun substTerm x x' (Path (PVar v)) =
        if x = v then Path x' else Path (PVar v)
    | substTerm x x' (Path (PPath (p, v))) =
        Path (PPath (substModexpr x x' p, v))
    | substTerm x x' (Lit l) = Lit l
    | substTerm x x' (Sort s) = Sort s
    | substTerm x x' (App (m1, m2)) =
        App (substTerm x x' m1, substTerm x x' m2)
    | substTerm x x' (Case (m1, pml, m2)) = raise Fail ""
    | substTerm x x' (IfElse (m1, m2, m3)) =
        IfElse (substTerm x x' m1, substTerm x x' m2, substTerm x x' m3)
    | substTerm x x' (Let (v, m1, m2, m3)) =
        Let (v, substTerm x x' m1, substTerm x x' m2, substTerm x x' m3)
    | substTerm x x' (Lambda (v, m1, m2)) =
        Lambda (v, substTerm x x' m1, substTerm x x' m2)
    | substTerm x x' (DepProduct (v, m1, m2)) =
        DepProduct (v, substTerm x x' m1, substTerm x x' m2)

    and substDef x x' (DefVal m) = DefVal (substTerm x x' m)
    | substDef x x' (DefData (m, nml)) =
        DefData (substTerm x x' m, map (fn (n, m') => (n, substTerm x x' m')) nml)
    | substDef x x' (DefMod m) = DefMod (substModexpr x x' m)
    | substDef x x' (DefModSig (m1, m2)) =
        DefModSig (substModexpr x x' m1, substModtype x x' m2)
    | substDef x x' (DefModTransparent m) = DefModTransparent (substModexpr x x' m)
    and substSpec x x' (SpecAbsMod m) = SpecAbsMod (substModtype x x' m)
    | substSpec x x' (SpecManifestMod (m1, m2)) =
        SpecManifestMod (substModtype x x' m1,
        substModexpr x x' m2)
    | substSpec x x' (SpecAbsTerm m) = SpecAbsTerm (substTerm x x' m)
    | substSpec x x' (SpecManifestTerm (m1, m2)) =
        SpecManifestTerm (substTerm x x' m1, substTerm x x' m2)
    and substModtype x x' (ModTypeSig sl) =
        ModTypeSig (map (fn ((v1, v2), s) => ((v1, v2), substSpec x x' s)) sl)
    | substModtype x x' (ModTypeFunctor (v, m1, m2)) =
        ModTypeFunctor (v, substModtype x x' m1, substModtype x x' m2)
    and substModexpr x x' (ModStruct ml) =
        ModStruct (map (fn ((v1, v2), d) => ((v1, v2), substDef x x' d)) ml)
    | substModexpr x x' (ModFunctor (v, m1, m2)) =
        ModFunctor (v, substModtype x x' m1, substModexpr x x' m2)
    | substModexpr x x' (ModApp (m1, m2)) =
        ModApp (substModexpr x x' m1, substModexpr x x' m2)
    | substModexpr x x' (ModPath (PPath (m, v))) =
        ModPath (PPath (substModexpr x x' m, v))
    | substModexpr x x' (ModPath (PVar v)) =
        if x = v then ModPath x' else ModPath (PVar v)
  end

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

  and mexpreq (ModStruct ml) (ModStruct ml') = raise Fail ""
  | mexpreq (ModFunctor (v, m1, m2)) (ModFunctor (v', m1', m2')) =
      if eqv v v' then mtypeeq m1 m1' andalso mexpreq m2 m2'
      else mtypeeq m1 m1' andalso mexpreq m2 (PSub.substModexpr v' (PVar v) m2')
  | mexpreq (ModApp (m1, m2)) (ModApp (m1', m2')) =
      mexpreq m1 m1' andalso mexpreq m2 m2'
  | mexpreq (ModPath (PPath (m, v))) (ModPath (PPath (m', v'))) =
      mexpreq m m' andalso eqv v v'
  | mexpreq (ModPath (PVar v)) (ModPath (PVar v')) = eqv v v'
  | mexpreq _ _ = false
  and mtypeeq (ModTypeSig sl) (ModTypeSig sl') = false
  | mtypeeq (ModTypeFunctor (v, m1, m2)) (ModTypeFunctor (v', m1', m2')) =
      if eqv v v' then mtypeeq m1 m1' andalso mtypeeq m2 m2'
      else mtypeeq m1 m1' andalso mtypeeq m2 (PSub.substModtype v' (PVar v) m2')

end

