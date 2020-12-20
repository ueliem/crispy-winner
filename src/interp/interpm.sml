structure MTSInterpM : sig
  include INTERPM
  val bindAbsTerm : MTS.var -> MTS.term -> 'a monad -> 'a monad
  val bindManifestTerm : MTS.var -> MTS.term -> MTS.term
    -> 'a monad -> 'a monad
  val bindAbsMod : MTS.var -> MTS.modtype -> 'a monad -> 'a monad
  val bindManifestMod : MTS.var -> MTS.modtype -> MTS.modexpr
    -> 'a monad -> 'a monad
  val registerSort : MTS.sort -> unit monad
  val registerAxiom : MTS.sort -> MTS.sort -> unit monad
  val registerRule : MTS.sort -> MTS.sort -> MTS.sort -> unit monad
  val getSorts : unit -> MTS.sorts monad
  val getAxioms : unit -> MTS.ax monad
  val getRules : unit -> MTS.rules monad
  val getDefModexpr : MTS.def -> MTS.modexpr monad
  val getDefTerm : MTS.def -> MTS.term monad
  val getSpecTerm : MTS.specification -> MTS.term monad
  val getSpecType : MTS.specification -> MTS.term monad
  val getSpecModexpr : MTS.specification -> MTS.modexpr monad
  val getSpecModtype : MTS.specification -> MTS.modtype monad
  val field : MTS.path -> (MTS.var * MTS.specification) list
    -> MTS.specification monad
  structure Util : MUTIL
end = struct
  structure InterpM = InterpMT (structure S = struct
    type enventry = MTS.specification
    type s = MTS.sorts * MTS.ax * MTS.rules
    type e = unit
  end; structure M = MTSCompilerM)
  structure Util = MUtil (structure M = InterpM)
  open InterpM
  open Util
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
    | getDefModexpr (DefMod m) = return m
    | getDefModexpr (DefModSig (m1, m2)) = return m1
    | getDefModexpr (DefModTransparent m) = return m
  fun getDefTerm (DefVal m) = return m
    | getDefTerm (DefMod m) = throw ()
    | getDefTerm (DefModSig (m1, m2)) = throw ()
    | getDefTerm (DefModTransparent m) = throw ()
  fun getSpecTerm s =
    (case s of
      SpecManifestTerm (_, m) => return m
    | _ => throw ())
  fun getSpecType s = (case s of
      SpecAbsTerm m => return m
    | SpecManifestTerm (m, _) => return m
    | _ => throw ())
  fun getSpecModexpr s =
    (case s of
      SpecManifestMod (_, m) => return m
    | _ => throw ())
  fun getSpecModtype s =
    (case s of
      SpecAbsMod m => return m
    | SpecManifestMod (m, _) => return m
    | _ => throw ())
  fun field _ ([]) = throw ()
    | field (PVar _) _ = throw ()
    | field (PPath (p, v)) ((x, s)::xs) =
      if eqv v x then return s
      else field (PPath (p, v))
        (map (fn (x', s') => (x', PSub.substSpec x
          (PPath (p, x)) s')) xs)
end
