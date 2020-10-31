structure Defs : sig
  include MONADZEROPLUS where type 'a monad = 'a InterpM.monad
  val allDiff : MTS.var list -> unit monad
  val wfModtype : MTS.modtype -> unit monad
  val wfSpec : MTS.specification -> unit monad
  val cModexpr : MTS.modexpr -> MTS.modtype monad
  val ptModexpr : MTS.modexpr -> MTS.modtype monad
  val qpModexpr : MTS.modexpr -> MTS.modtype monad

  val cPath : MTS.path -> MTS.modtype monad
  val ptPath : MTS.path -> MTS.modtype monad
  val qpPath : MTS.path -> MTS.modtype monad

  (* val ptSpec 
  val qpSpec 

  val cDef d *)
  val qpDef : MTS.def -> MTS.specification monad

  val subcModtype : MTS.modtype -> MTS.modtype -> unit monad
  val subcSpec : MTS.specification -> MTS.specification -> unit monad

  val strSpec : MTS.path -> MTS.specification -> MTS.specification
  val strModtype : MTS.path -> MTS.modtype -> MTS.modtype
  
end
=
struct
  open InterpM
  open MTS
  open MTSCheck

  fun allDiff ([]) = throw ()
  | allDiff (x::xs) =
      let fun f _ ([]) = return ()
      | f ys' (y::ys) =
          (case List.find (fn y' => eqv y y') ys' of
            SOME _ => zero ()
          | NONE => f (y::ys') ys)
      in f [x] xs end

  fun wfModtype (ModTypeSig sl) =
      let fun wfSigbody ([]) = return ()
      | wfSigbody ((v, s)::sl') = wfSpec s >>= (fn _ =>
          bindSpec v s (wfSigbody sl'))
      in
        allDiff (#1 (ListPair.unzip sl)) >>= (fn _ =>
        wfSigbody sl)
      end
  | wfModtype (ModTypeFunctor (v, m1, m2)) =
      wfModtype m1 >>= (fn _ => bindAbsMod v m1 (wfModtype m2))
  and wfSpec (SpecAbsMod m) = wfModtype m
  | wfSpec (SpecManifestMod (m1, m2)) =
      wfModtype m1 >>= (fn _ => cModexpr m2 >>= (fn _ => return ()))
  | wfSpec (SpecAbsTerm m) =
      whsdcl m >>= (fn m' => isSort m' >>= (fn _ => return ()))
  | wfSpec (SpecManifestTerm (m1, m2)) =
      whsdcl m2 >>= (fn m2' => bequiv m1 m2')

  and cModexpr m = raise Fail ""
  and ptModexpr m = raise Fail ""
  and qpModexpr (ModStruct dl) =
      let fun cbody ([]) = return ([])
      | cbody ((v, d)::dl') =
          qpDef d >>= (fn s =>
          bindSpec v s (cbody dl') >>= (fn sl =>
          return ((v, s)::sl)))
      in
        allDiff (#1 (ListPair.unzip dl)) >>= (fn _ =>
        cbody dl >>= (fn vsl => return (ModTypeSig vsl)))
      end
  | qpModexpr (ModFunctor (v, m1, m2)) =
      wfModtype m1 >>= (fn _ =>
      bindAbsMod v m1 (qpModexpr m2) >>= (fn m2' =>
      return (ModTypeFunctor (v, m1, m2'))))
  | qpModexpr (ModApp (m1, m2)) =
      qpModexpr m1 >>= (fn m1' =>
      cModexpr m2 >>= (fn m2' =>
      isFuncT m1' >>= (fn (v, m1'', m2'') =>
      return (substModtype v m2 m2''))))
  | qpModexpr (ModPath (PVar v)) =
      raise Fail ""
  | qpModexpr (ModPath (PPath (p, v))) =
      qpModexpr p >>= (fn s =>
      isSig s >>= (fn s' =>
      raise Fail ""
      ))
  (* | qpModexpr (ModPath p) =
      resolvePath p >>= (fn s => (case s of
        SpecAbsMod m => return m
      | SpecManifestMod (m, _) => return m
      | _ => throw ())) *)

  and cPath p s = raise Fail ""
  and ptPath p = raise Fail ""
  and qpPath (PVar v) =
      raise Fail ""
  | qpPath (PPath (p, v)) =
      raise Fail ""

  and ptSpec s = raise Fail ""
  and qpSpec s = raise Fail ""

  and cDef d = raise Fail ""
  and qpDef (DefVal m) = raise Fail ""
  | qpDef (DefData (m1, nml)) = raise Fail ""
  | qpDef (DefMod m) = raise Fail ""
  | qpDef (DefModSig (m1, m2)) = raise Fail ""
  | qpDef (DefModTransparent m) = raise Fail ""

  and subcModtype m1 m2 = raise Fail ""
  and subcSpec s1 s2 = raise Fail ""

  and strSpec p (SpecAbsMod m) = SpecManifestMod (strModtype p m, ModPath p)
  | strSpec p (SpecManifestMod (m1, m2)) = SpecManifestMod (m1, m2)
  | strSpec p (SpecAbsTerm m) = SpecManifestTerm (m, Path p)
  | strSpec p (SpecManifestTerm (m1, m2)) = SpecManifestTerm (m1, m2)

  and strModtype p (ModTypeSig sl) =
      ModTypeSig (map (fn (v, s) => (v, strSpec p s)) sl)
  | strModtype p (ModTypeFunctor (v, m1, m2)) =
      ModTypeFunctor (v, m1, strModtype (PFunc (p, PVar v)) m2)

end
