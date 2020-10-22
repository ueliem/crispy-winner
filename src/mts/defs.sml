structure Defs : sig
  include MONADZEROPLUS where type 'a monad = 'a InterpM.monad
  val allDiff : MTS.var list -> unit monad
  val wfDef : MTS.def -> unit monad
  val wfModtype : MTS.modtype -> unit monad
  val wfSpec : MTS.specification -> unit monad
  val wfModexpr : MTS.modexpr -> unit monad
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

  fun wfDef (DefVal m) = raise Fail ""
  | wfDef (DefData _) = raise Fail ""
  | wfDef (DefMod m) = wfModexpr m
  | wfDef (DefModSig (m1, m2)) = raise Fail ""
      (* wfModexpr m1 >>= (fn _ => bindManifestMod v m1 (wfModtype m2)) *)
  | wfDef (DefModTransparent m) = wfModexpr m
  and wfModtype (ModTypeSig sl) =
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
  | wfSpec (SpecManifestMod (m1, m2)) = wfModtype m1 >>= (fn _ => wfModexpr m2)
  | wfSpec (SpecAbsTerm m) =
      whsdcl m >>= (fn m' => isSort m' >>= (fn _ => return ()))
  | wfSpec (SpecManifestTerm (m1, m2)) =
      whsdcl m2 >>= (fn m2' => bequiv m1 m2')
  and wfModexpr (ModStruct dl) = raise Fail ""
  | wfModexpr (ModFunctor (v, m1, m2)) = raise Fail ""
  | wfModexpr (ModApp (m1, m2)) = wfModexpr m1 >>= (fn _ => wfModexpr m2)
  | wfModexpr (ModPath m) = raise Fail ""

end
