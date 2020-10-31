structure MTSCheck : sig
  include MONADZEROPLUS where type 'a monad = 'a InterpM.monad
  val isSort : MTS.term -> MTS.sort monad
  val isBottomSort : MTS.sort -> unit monad
  val isTopSort : MTS.sort -> unit monad
  val hasAxiom : MTS.sort -> MTS.sort monad
  val hasRule : MTS.sort -> MTS.sort -> MTS.sort monad
  val startsRule : MTS.sort -> unit monad

  val plus : MTS.sort -> MTS.sort monad
  val minus : MTS.sort -> MTS.sort monad
  val rho : MTS.sort -> MTS.sort -> MTS.sort monad
  val mu : MTS.sort -> MTS.sort -> MTS.sort monad
  val elmtclass : MTS.term -> MTS.sort monad
  val sortclass : MTS.term -> MTS.sort monad

  val whsdcl : MTS.term -> MTS.term monad
  val sdcl : MTS.term -> MTS.term monad

  val allDiff : MTS.var list -> unit monad
  val wfModtype : MTS.modtype -> unit monad
  val wfSpec : MTS.specification -> unit monad
  val cModexpr : MTS.modexpr -> MTS.modtype monad
  val ptModexpr : MTS.modexpr -> MTS.modtype monad
  val qpModexpr : MTS.modexpr -> MTS.modtype monad

  val cPath : MTS.path -> MTS.specification monad
  val ptPath : MTS.path -> MTS.specification monad
  val qpPath : MTS.path -> MTS.specification monad

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

  fun isSort (Sort s) =
    getSorts () >>= (fn srts =>
      if List.exists (fn x => x = s) srts
      then return s else throw ())
  | isSort _ = throw ()

  fun isBottomSort srt =
    getSorts () >>= (fn srts =>
    getAxioms () >>= (fn axs =>
      if List.exists (fn (s1, s2) => s2 = srt) axs
      then throw () else return ()))

  fun isTopSort srt =
    getSorts () >>= (fn srts =>
    getAxioms () >>= (fn axs =>
      if List.exists (fn (s1, s2) => s1 = srt) axs
      then throw () else return ()))

  fun hasAxiom s1 =
    getAxioms () >>= (fn axs =>
      (case List.find (fn (s1', s2) => s1 = s1') axs of
        SOME (s1, s2) => return s2
      | NONE => throw ()))

  fun hasRule s1 s2 =
    getRules () >>= (fn rls =>
      (case List.find (fn (s1', s2', s3) => s1 = s1' andalso s2 = s2') rls of
        SOME (s1, s2, s3) => return s3
      | NONE => throw ()))

  fun startsRule s1 =
    getRules () >>= (fn rls =>
      (case List.find (fn (s1', s2', s3) => s1 = s1') rls of
        SOME (s1, s2, s3) => return ()
      | NONE => throw ()))

  fun plus s1 =
    getstate >>= (fn (srts, axs, rls) =>
      (case List.find (fn (s1', s2) => s1 = s1') axs of
        SOME (s1, s2) => return s2
      | NONE => zero ()))

  fun minus s2 =
    getstate >>= (fn (srts, axs, rls) =>
      (case List.find (fn (s1, s2') => s2 = s2') axs of
        SOME (s1, s2) => return s1
      | NONE => throw ()))

  fun rho s1 s2 =
    getstate >>= (fn (srts, axs, rls) =>
      (case List.find (fn (s1', s2', s3) => s1 = s1' andalso s2 = s2') rls of
        SOME (s1, s2, s3) => return s3
      | NONE => throw ()))

  fun mu s1 s2 =
    getstate >>= (fn (srts, axs, rls) =>
      (case List.find (fn (s1', s3, s2') => s1 = s1' andalso s2 = s2') rls of
        SOME (_, s3, _) => return s3
      | NONE => throw ()))

  fun elmtclass (Path (PVar v)) =
      getTy v >>= (fn m =>
      trimEnv v (sortclass m))
  | elmtclass (Path p) =
      resolvePath p >>= (fn s =>
      isTermTy s >>= (fn m =>
      trimEnv (pathHead p) (sortclass m)))
  | elmtclass (Lit (IntLit _)) = return TypeVal
  | elmtclass (Lit (IntTyLit)) = return KindVal
  | elmtclass (Lit (BoolLit _)) = return TypeVal
  | elmtclass (Lit (BoolTyLit)) = return KindVal
  | elmtclass (Sort s) =
      sortclass (Sort s) >>= plus
  | elmtclass (App (m1, m2)) =
      elmtclass m1 >>= (fn s1 =>
      elmtclass m2 >>= (fn s2 => mu s1 s2))
  | elmtclass (Case (m1, pml, m2)) = raise Fail ""
  | elmtclass (IfElse (m1, m2, m3)) =
      elmtclass m2 >>= (fn s2 =>
      elmtclass m3 >>= (fn s3 =>
        if s2 = s3 then return s2 else zero ()))
  | elmtclass (Let (v, m1, m2, m3)) =
      bindManifestTerm v m1 m2 (elmtclass m3)
  | elmtclass (Lambda (v, m1, m2)) =
      elmtclass m1 >>= (fn s1 =>
      bindAbsTerm v m1 (elmtclass m2) >>= (fn s2 => rho s1 s2))
  | elmtclass (DepProduct (v, m1, m2)) =
      sortclass (DepProduct (v, m1, m2)) >>= plus

  and sortclass (Path (PVar v)) = elmtclass (Path (PVar v)) >>= minus
  | sortclass (Path p) = elmtclass (Path p) >>= minus
  | sortclass (Lit (IntLit _)) = zero ()
  | sortclass (Lit (IntTyLit)) = return TypeVal
  | sortclass (Lit (BoolLit _)) = zero ()
  | sortclass (Lit (BoolTyLit)) = return TypeVal
  | sortclass (Sort s) = plus s
  | sortclass (App (m1, m2)) = elmtclass (App (m1, m2)) >>= minus
  | sortclass (Case (m1, pml, m2)) = raise Fail ""
  | sortclass (IfElse (m1, m2, m3)) =
      sortclass m2 >>= (fn s2 =>
      sortclass m3 >>= (fn s3 =>
        if s2 = s3 then return s2 else zero ()))
  | sortclass (Let (v, m1, m2, m3)) =
      bindManifestTerm v m1 m2 (sortclass m3)
  | sortclass (Lambda (v, m1, m2)) =
      elmtclass (Lambda (v, m1, m2)) >>= minus
  | sortclass (DepProduct (v, m1, m2)) =
      sortclass m1 >>= (fn s1 =>
      bindAbsTerm v m1 (sortclass m2) >>= (fn s2 => rho s1 s2))

  fun whsdcl m =
    sdcl m >>= (fn m' => whreduce m' >>= (fn m'' => return m''))
  and sdcl (Path (PVar v)) =
      getTy v >>= (fn m =>
      whsdcl m >>= (fn m' =>
      isSort m' >>= (fn _ =>
      return m)))
  | sdcl (Path p) =
      resolvePath p >>= (fn s =>
      isTermTy s)
  | sdcl (Lit (IntLit _)) = return (Lit (IntTyLit))
  | sdcl (Lit (BoolLit _)) = return (Lit (BoolTyLit))
  | sdcl (Lit (IntTyLit)) = return (Sort TypeVal)
  | sdcl (Lit (BoolTyLit)) = return (Sort TypeVal)
  | sdcl (Sort s) = hasAxiom s >>= (fn s' => return (Sort s'))
  | sdcl (App (m1, m2)) =
      whsdcl m1 >>= (fn m1' =>
      sdcl m2 >>= (fn m2' =>
      isDepProduct m2' >>= (fn (v, m1'', m2'') => return (subst v m2 m2''))))
  | sdcl (Case (m1, pml, m2)) = raise Fail ""
  | sdcl (IfElse (m1, m2, m3)) =
      sdcl m1 >>= (fn m1' =>
      whsdcl m2 >>= (fn m2' =>
      whsdcl m3 >>= (fn m3' =>
      bequiv m2' m3' >>= (fn _ =>
      isBoolTy m1' >>= (fn _ => return m2')))))
  | sdcl (Let (v, m1, m2, m3)) =
      whsdcl m1 >>= (fn m1' =>
      isSort m1' >>= (fn _ =>
      whsdcl m2 >>= (fn m2' =>
      bequiv m1 m2' >>= (fn _ =>
      bindManifestTerm v m1 m2 (whsdcl m3) >>= (fn m3' =>
      return (Let (v, m1, m2, m3')))))))
  | sdcl (Lambda (v, m1, m2)) =
      elmtclass (Lambda (v, m1, m2)) >>= (fn _ =>
      bindAbsTerm v m1 (sdcl m2) >>= (fn m2' =>
      return (DepProduct (v, m1, m2'))))
  | sdcl (DepProduct (v, m1, m2)) =
      sortclass m1 >>= (fn s1 =>
      bindAbsTerm v m1 (whsdcl m2 >>= (fn m2' => isSort m2')) >>= (fn s2 =>
      rho s1 s2 >>= (fn s3 => return (Sort s3))))

  and allDiff ([]) = throw ()
  | allDiff (x::xs) =
      let fun f _ ([]) = return ()
      | f ys' (y::ys) =
          (case List.find (fn y' => eqv y y') ys' of
            SOME _ => zero ()
          | NONE => f (y::ys') ys)
      in f [x] xs end

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
  | qpModexpr (ModPath p) =
      qpPath p >>= (fn s => (case s of
        SpecAbsMod m => return m
      | SpecManifestMod (m, _) => return m
      | _ => throw ()))
  (* | qpModexpr (ModPath (PPath (p, v))) =
      qpModexpr p >>= (fn s =>
      isSig s >>= (fn s' =>
      raise Fail ""
      ))
  | qpModexpr (ModPath p) =
      resolvePath p >>= (fn s => (case s of
        SpecAbsMod m => return m
      | SpecManifestMod (m, _) => return m
      | _ => throw ())) *)

  and cPath p s = raise Fail ""
  and ptPath p = raise Fail ""
  and qpPath (PVar v) =
      getSpec v >>= (fn _ =>
      raise Fail "")
  | qpPath (PPath (m, v)) =
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

