structure InterpMTS = InterpMT (structure S = struct
  type var = MTS.var
  type enventry = MTS.specification
  type s = MTS.sorts * MTS.ax * MTS.rules
  type e = unit
  val eqv = MTS.eqv
end)

structure InterpMTSUtil = MUtil (structure M = InterpMTS)

structure InterpM : sig
  include INTERPM
  val bindAbsTerm : MTS.var -> MTS.term -> 'a monad -> 'a monad
  val bindManifestTerm : MTS.var -> MTS.term -> MTS.term -> 'a monad -> 'a monad
  val bindAbsMod : MTS.var -> MTS.modtype -> 'a monad -> 'a monad
  val bindManifestMod : MTS.var -> MTS.modtype -> MTS.modexpr -> 'a monad -> 'a monad

  val registerSort : MTS.sort -> unit monad
  val registerAxiom : MTS.sort -> MTS.sort -> unit monad
  val registerRule : MTS.sort -> MTS.sort -> MTS.sort -> unit monad
  
  val getSorts : unit -> MTS.sorts monad
  val getAxioms : unit -> MTS.ax monad
  val getRules : unit -> MTS.rules monad

  val getSpecType : MTS.specification -> MTS.term monad
  val getSpecModtype : MTS.specification -> MTS.modtype monad
  val getDefModexpr : MTS.def -> MTS.modexpr monad
  val getDefTerm : MTS.def -> MTS.term monad

  val field : MTS.path -> ((MTS.var * MTS.var) * MTS.specification) list
    -> MTS.specification monad
end
=
struct
  open InterpMTS
  open InterpMTSUtil
  open MTS

  fun registerSort srt =
    getstate >>= (fn (srts, axs, rls) =>
    putstate (srt::srts, axs, rls))
  fun registerAxiom s1 s2 =
    getstate >>= (fn (srts, axs, rls) =>
    putstate (srts, (s1, s2)::axs, rls))
  fun registerRule s1 s2 s3 =
    getstate >>= (fn (srts, axs, rls) =>
    putstate (srts, axs, (s1, s2, s3)::rls))

  fun getSorts () = getstate >>= (fn (srts, axs, rls) => return srts)
  fun getAxioms () = getstate >>= (fn (srts, axs, rls) => return axs)
  fun getRules () = getstate >>= (fn (srts, axs, rls) => return rls)

  fun bindAbsTerm v m = bindEntry v (SpecAbsTerm m)
  fun bindManifestTerm v m1 m2 = bindEntry v (SpecManifestTerm (m1, m2))
  fun bindAbsMod v m = bindEntry v (SpecAbsMod m)
  fun bindManifestMod v m1 m2 = bindEntry v (SpecManifestMod (m1, m2))

  fun getDefModexpr (DefVal m) = throw ()
  | getDefModexpr (DefData _) = throw ()
  | getDefModexpr (DefMod m) = return m
  | getDefModexpr (DefModSig (m1, m2)) = return m1
  | getDefModexpr (DefModTransparent m) = return m

  fun getDefTerm (DefVal m) = return m
  | getDefTerm (DefData _) = throw ()
  | getDefTerm (DefMod m) = throw ()
  | getDefTerm (DefModSig (m1, m2)) = throw ()
  | getDefTerm (DefModTransparent m) = throw ()

  fun getSpecType s =
    (case s of
      SpecAbsTerm m => return m
    | SpecManifestTerm (m, _) => return m
    | _ => throw ())

  fun getSpecModtype s =
    (case s of
      SpecAbsMod m => return m
    | SpecManifestMod (m, _) => return m
    | _ => throw ())

  fun field _ ([]) = throw ()
  | field (PVar _) _ = throw ()
  | field (PPath (p, v)) (((x', _), s)::xs) =
      if eqv v x' then return s
      else field (PPath (p, v))
        (map (fn ((x'', x'''), s') => ((x'', x'''), PSub.substSpec x'
          (PPath (p, x')) s')) xs)

end

