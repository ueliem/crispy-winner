functor SUBST (structure S : sig
  type r
  val replaceVTerm : MTS.var -> r -> MTS.term
  val replaceVModexpr : MTS.var -> r -> MTS.modexpr
end) : sig
  type r
  val substTerm : MTS.var -> r -> MTS.term -> MTS.term
  val substDef : MTS.var -> r -> MTS.def -> MTS.def
  val substSpec : MTS.var -> r -> MTS.specification -> MTS.specification
  val substModtype : MTS.var -> r -> MTS.modtype -> MTS.modtype
  val substModexpr : MTS.var -> r -> MTS.modexpr -> MTS.modexpr
end
=
struct
  type r = S.r
  open MTS

  fun substTerm x x' (Path (PVar v)) =
    if eqv x v then S.replaceVTerm x x' else Path (PVar v)
    | substTerm x x' (Path (PPath (p, v))) =
      Path (PPath (substModexpr x x' p, v))
    | substTerm x x' (Lit l) = Lit l
    | substTerm x x' (Sort s) = Sort s
    | substTerm x x' (App (m1, m2)) =
      App (substTerm x x' m1, substTerm x x' m2)
    | substTerm x x' (Case (m1, m2, pml)) =
      Case (substTerm x x' m1, substTerm x x' m2,
        map (fn m => substTerm x x' m) pml)
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
    | substTerm x x' (Fix (v, m1, m2)) =
      if eqv x v then Fix (v, m1, m2)
      else Fix (v, substTerm x x' m1, substTerm x x' m2)
    | substTerm x x' (Inductive ((v, t), tl)) =
      if eqv x v then Inductive ((v, t), tl)
      else Inductive ((v, substTerm x x' t), map (substTerm x x') tl)
    | substTerm x x' (Constr (i, t)) = Constr (i, substTerm x x' t)
  and substDef x x' (DefVal m) = DefVal (substTerm x x' m)
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
      | f sl'' ((v, s)::sl') =
          if eqv x v then
            (List.rev sl'') @ ((v, s)::sl')
          else
            f ((v, substSpec x x' s)::sl'') sl'
      in ModTypeSig (f [] sl) end
    | substModtype x x' (ModTypeFunctor (v, m1, m2)) =
      if eqv x v then (ModTypeFunctor (v, m1, m2))
      else ModTypeFunctor (v, substModtype x x' m1, substModtype x x' m2)
  and substModexpr x x' (ModStruct ml) =
    let fun f ml'' ([]) = ml''
      | f ml'' ((v, d)::ml') =
          if eqv x v then
            (List.rev ml'') @ ((v, d)::ml')
          else
            f ((v, substDef x x' d)::ml'') ml'
      in ModStruct (f [] ml) end
    | substModexpr x x' (ModFunctor (v, m1, m2)) =
      if eqv x v then (ModFunctor (v, m1, m2))
      else ModFunctor (v, substModtype x x' m1, substModexpr x x' m2)
    | substModexpr x x' (ModApp (m1, m2)) =
      ModApp (substModexpr x x' m1, substModexpr x x' m2)
    | substModexpr x x' (ModPath (PPath (m, v))) =
      ModPath (PPath (substModexpr x x' m, v))
    | substModexpr x x' (ModPath (PVar v)) =
      if eqv x v then S.replaceVModexpr x x'
      else ModPath (PVar v)
end

structure VSub = SUBST (structure S = struct
  type r = MTS.var
  fun replaceVTerm v v' = MTS.Path (MTS.PVar v')
  fun replaceVModexpr v v' = MTS.ModPath (MTS.PVar v')
end)

structure MSub = SUBST (structure S = struct
  type r = MTS.modexpr
  fun replaceVTerm v m = raise Fail "cannot substitute modexpr for var in term"
  fun replaceVModexpr v m = m
end)

structure PSub = SUBST (structure S = struct
  type r = MTS.path
  fun replaceVTerm v p = MTS.Path p
  fun replaceVModexpr v p = MTS.ModPath p
end)

structure TSub = SUBST (structure S = struct
  type r = MTS.term
  fun replaceVTerm v t = t
  fun replaceVModexpr v t = raise Fail "cannot substitute term for var in modexpr"
end)

