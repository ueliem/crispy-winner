structure PseudoType : sig
  type 'a monad = 'a MTSInterpM.monad
  val pseudoTModexpr : MTS.modexpr -> MTS.specification monad
  val pseudoTPath : MTS.path -> MTS.specification monad
  val pseudoSpec : MTS.path -> MTS.specification monad
end = struct
  type 'a monad = 'a MTSInterpM.monad
  open MTS
  open MTSInterpM
  fun pseudoTModexpr (ModStruct dl) =
    let fun f ([]) = return []
      | f ((v, d)::dl') =
        (case d of
          DefVal m => return [(v, SpecManifestTerm (m, m))]
        | DefMod m => pseudoTModexpr m >>= (fn m' =>
            return [(v, m')])
        | DefModSig (m1, m2) => return [(v, SpecAbsMod m2)]
        | DefModTransparent m =>
            return [(v, SpecManifestMod (ModTypeSig [], m))]
        ) >>= (fn vsl =>
        bindMany vsl (f dl') >>= (fn sl =>
        return (vsl @ sl)))
    in f dl >>= (fn sl =>
      return (SpecAbsMod (ModTypeSig sl))) end
    | pseudoTModexpr (ModFunctor (v, m1, m2)) =
      bindAbsMod v m1 (pseudoTModexpr m2) >>= (fn s =>
      getSpecModtype s >>= (fn m2' =>
      return (SpecAbsMod (ModTypeFunctor (v, m1, m2')))))
    | pseudoTModexpr (ModApp (m1, m2)) =
      pseudoTModexpr m1 >>= (fn s =>
      getSpecModtype s >>= (fn m1' =>
      Term.isFuncT m1' >>= (fn (v, _, m3) =>
      return (SpecAbsMod (MSub.substModtype v m2 m3)))))
    | pseudoTModexpr (ModPath p) = pseudoTPath p
  and pseudoTPath (PVar v) = getEntry v
    | pseudoTPath (PPath (p, v)) =
      pseudoTModexpr p >>= (fn s =>
      getSpecModtype s >>= (fn s' =>
      Term.isSig s' >>= (fn s'' =>
      field (PPath (p, v)) s'')))
  fun pseudoSpec (PPath (p, v)) =
    pseudoTModexpr p >>= (fn s =>
    getSpecModtype s >>= (fn s' =>
    Term.isSig s' >>= (fn s'' =>
    Term.sigbodyContains v s'')))
    | pseudoSpec (PVar v) = zero ()
end
