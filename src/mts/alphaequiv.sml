structure Equiv : sig
  val eq : MTS.term -> MTS.term -> bool
  val mexpreq : MTS.modexpr -> MTS.modexpr -> bool
  val mtypeeq : MTS.modtype -> MTS.modtype -> bool
end
=
struct
  open MTS

  fun eq (Path p) (Path p') = patheq p p'
  | eq (Lit l) (Lit l') = l = l'
  | eq (Sort s) (Sort s') = s = s'
  | eq (App (m1, m2)) (App (m1', m2')) = eq m1 m1' andalso eq m2 m2'
  | eq (Case (m1, m2, pml)) (Case (m1', m2', pml')) =
      eq m1 m1' andalso eq m2 m2'
      andalso foldl (fn ((m, m'), x) => x andalso eq m m')
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
        andalso eq m3 (TSub.substTerm v' (Path (PVar v)) m3')
  | eq (Lambda (AnonVar, m1, m2)) (Lambda (_, m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (Lambda (_, m1, m2)) (Lambda (AnonVar, m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (Lambda (v, m1, m2)) (Lambda (v', m1', m2')) =
      if eqv v v' then eq m1 m1' andalso eq m2 m2'
      else eq m1 m1' andalso eq m2 (TSub.substTerm v' (Path (PVar v)) m2')
  | eq (DepProduct (AnonVar, m1, m2)) (DepProduct (_, m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (DepProduct (_, m1, m2)) (DepProduct (AnonVar, m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (DepProduct (v, m1, m2)) (DepProduct (v', m1', m2')) =
      if eqv v v' then eq m1 m1' andalso eq m2 m2'
      else eq m1 m1' andalso eq m2 (TSub.substTerm v' (Path (PVar v)) m2')
  | eq (Fix (AnonVar, m1, m2)) (Fix (_, m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (Fix (_, m1, m2)) (Fix (AnonVar, m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (Fix (v, m1, m2)) (Fix (v', m1', m2')) =
      if eqv v v' then eq m1 m1' andalso eq m2 m2'
      else eq m1 m1' andalso eq m2 (TSub.substTerm v' (Path (PVar v)) m2')
  | eq _ _ = false
  and mexpreq (ModStruct ml) (ModStruct ml') =
      foldl (fn (((v, d), (v', d')), x) => 
        x andalso eqv v v' andalso defeq d d')
        true (ListPair.zipEq (ml, ml'))
  | mexpreq (ModFunctor (v, m1, m2)) (ModFunctor (v', m1', m2')) =
      if eqv v v' then mtypeeq m1 m1' andalso mexpreq m2 m2'
      else mtypeeq m1 m1' andalso mexpreq m2 (PSub.substModexpr v' (PVar v) m2')
  | mexpreq (ModApp (m1, m2)) (ModApp (m1', m2')) =
      mexpreq m1 m1' andalso mexpreq m2 m2'
  | mexpreq (ModPath p) (ModPath p') = patheq p p'
  | mexpreq _ _ = false
  and mtypeeq (ModTypeSig sl) (ModTypeSig sl') =
      foldl (fn (((v, s), (v', s')), x) => 
        x andalso eqv v v' andalso speceq s s')
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
  | defeq (DefModSig (m1, m2)) (DefModSig (m1', m2')) =
      mexpreq m1 m1' andalso mtypeeq m2 m2'
  | defeq (DefModTransparent m) (DefModTransparent m') = mexpreq m m'
  | defeq _ _ = false
  and patheq (PVar v) (PVar v') = eqv v v'
  | patheq (PPath (m, v)) (PPath (m', v')) =
      mexpreq m m' andalso eqv v v'
  | patheq _ _ = false

end
