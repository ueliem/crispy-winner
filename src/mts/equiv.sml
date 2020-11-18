structure Equiv : sig
  val eq : MTS.term -> MTS.term -> bool
  val mexpreq : MTS.modexpr -> MTS.modexpr -> bool
  val mtypeeq : MTS.modtype -> MTS.modtype -> bool
end
=
struct
  open MTS

  fun eq (Path (PVar v)) (Path (PVar v')) = eqv v v'
  | eq (Path (PPath (p, v))) (Path (PPath (p', v'))) =
      mexpreq p p' andalso eqv v v'
  | eq (Lit l) (Lit l') = l = l'
  | eq (Sort s) (Sort s') = s = s'
  | eq (App (m1, m2)) (App (m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (Case (m, pml)) (Case (m', pml')) =
      eq m m' andalso foldl (fn (((c, vs, m1), (c', vs', m1')), x) => 
        x andalso eqv c c' andalso eqvs vs vs' andalso eq m1 m1')
        true (ListPair.zipEq (pml, pml'))
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
  and mexpreq (ModStruct ml) (ModStruct ml') =
      foldl (fn ((((v1, v2), d), ((v1', v2'), d')), x) => 
        x andalso eqv v2 v2' andalso defeq d d')
        true (ListPair.zipEq (ml, ml'))
  | mexpreq (ModFunctor (v, m1, m2)) (ModFunctor (v', m1', m2')) =
      if eqv v v' then mtypeeq m1 m1' andalso mexpreq m2 m2'
      else mtypeeq m1 m1' andalso mexpreq m2 (PSub.substModexpr v' (PVar v) m2')
  | mexpreq (ModApp (m1, m2)) (ModApp (m1', m2')) =
      mexpreq m1 m1' andalso mexpreq m2 m2'
  | mexpreq (ModPath (PPath (m, v))) (ModPath (PPath (m', v'))) =
      mexpreq m m' andalso eqv v v'
  | mexpreq (ModPath (PVar v)) (ModPath (PVar v')) = eqv v v'
  | mexpreq _ _ = false
  and mtypeeq (ModTypeSig sl) (ModTypeSig sl') =
      foldl (fn ((((v1, v2), s), ((v1', v2'), s')), x) => 
        x andalso eqv v2 v2' andalso speceq s s')
        true (ListPair.zipEq (sl, sl'))
  | mtypeeq (ModTypeFunctor (v, m1, m2)) (ModTypeFunctor (v', m1', m2')) =
      if eqv v v' then mtypeeq m1 m1' andalso mtypeeq m2 m2'
      else mtypeeq m1 m1' andalso mtypeeq m2 (PSub.substModtype v' (PVar v) m2')
  | mtypeeq _ _ = false
  and speceq (SpecAbsMod m) (SpecAbsMod m') = mtypeeq m m'
  | speceq (SpecManifestMod (m1, m2)) (SpecManifestMod (m1', m2')) =
      mtypeeq m1 m1' andalso mexpreq m2 m2'
  | speceq (SpecAbsTerm m) (SpecAbsTerm m') = eq m m'
  | speceq (SpecManifestTerm (m1, m2)) (SpecManifestTerm (m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | speceq _ _ = false
  and defeq (DefVal m) (DefVal m') = eq m m'
  | defeq (DefData (m, nml)) (DefData (m', nml')) =
      foldl (fn ((((v1, v2), t), ((v1', v2'), t')), x) => 
        x andalso eqv v2 v2' andalso eq t t')
        true (ListPair.zipEq (nml, nml'))

  | defeq (DefModSig (m1, m2)) (DefModSig (m1', m2')) =
      mexpreq m1 m1' andalso mtypeeq m2 m2'
  | defeq (DefModTransparent m) (DefModTransparent m') = mexpreq m m'
  | defeq _ _ = false

end
