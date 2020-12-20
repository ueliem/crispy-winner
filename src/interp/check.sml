structure MTSCheck : sig
  include MONADZEROPLUS where type 'a monad = 'a MTSInterpM.monad
  val isSort : MTS.term -> MTS.sort monad
  val isBottomSort : MTS.sort -> unit monad
  val isTopSort : MTS.sort -> unit monad
  val hasAxiom : MTS.sort -> MTS.sort monad
  val hasRule : MTS.sort -> MTS.sort -> MTS.sort monad
  val startsRule : MTS.sort -> unit monad
  val rho : MTS.sort -> MTS.sort -> MTS.sort monad
  val strSpec : MTS.path -> MTS.specification -> MTS.specification
  val strModtype : MTS.modexpr -> MTS.modtype -> MTS.modtype
  val domain : (MTS.var * MTS.specification) list
    -> MTS.var list
  val allDiff : MTS.var list -> unit monad
  val wfModtype : MTS.modtype -> unit monad
  val wfSpec : MTS.specification -> unit monad
  val cModexpr : MTS.modexpr -> MTS.modtype -> MTS.modtype monad
  val ptModexpr : MTS.modexpr -> MTS.modtype monad
  val qpModexpr : MTS.modexpr -> MTS.modtype monad
  val cPath : MTS.path -> MTS.specification -> MTS.specification monad
  val ptPath : MTS.path -> MTS.specification monad
  val qpPath : MTS.path -> MTS.specification monad
  val gammaRestr : MTS.var list
    -> (MTS.var * MTS.specification) list
    -> (MTS.var * MTS.specification) list monad
  val subcModtype : MTS.modtype -> MTS.modtype -> unit monad
  val subcSpec : MTS.specification -> MTS.specification -> unit monad
  val cTerm : MTS.term -> MTS.term -> unit monad
  val ptTerm : MTS.term -> MTS.term monad
  val whptTerm : MTS.term -> MTS.term monad
  val lrsub : MTS.var -> MTS.term -> MTS.term -> MTS.term -> MTS.term -> MTS.term monad
end
=
struct
  open MTSInterpM
  open Util
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
      (case List.find (fn (s1', s2', s3) =>
        s1 = s1' andalso s2 = s2') rls of
        SOME (s1, s2, s3) => return s3
      | NONE => throw ()))
  fun startsRule s1 =
    getRules () >>= (fn rls =>
      (case List.find (fn (s1', s2', s3) => s1 = s1') rls of
        SOME (s1, s2, s3) => return ()
      | NONE => throw ()))
  fun rho s1 s2 =
    getRules () >>= (fn rls =>
      (case List.find (fn (s1', s2', s3) =>
        s1 = s1' andalso s2 = s2') rls of
        SOME (s1, s2, s3) => return s3
      | NONE => throw ()))
  fun strSpec m' (SpecAbsMod m) =
      SpecManifestMod (strModtype (ModPath m') m, ModPath m')
    | strSpec m' (SpecManifestMod (m1, m2)) =
      SpecManifestMod (strModtype (ModPath m') m1, m2)
    | strSpec m' (SpecAbsTerm m) = SpecManifestTerm (m, Path m')
    | strSpec m' (SpecManifestTerm (m1, m2)) =
      SpecManifestTerm (m1, m2)
  and strModtype m' (ModTypeSig sl) =
      ModTypeSig (map (fn (v, s) =>
        (v, strSpec (PPath (m', v)) s)) sl)
    | strModtype m' (ModTypeFunctor (v, m1, m2)) =
      ModTypeFunctor (v, m1, strModtype (ModApp (m', ModPath (PVar v))) m2)
  fun domain sl = (#1 (ListPair.unzip sl))
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
        | wfSigbody ((v, s)::sl') =
          wfSpec s >> bindEntry v s (wfSigbody sl')
      in allDiff (domain sl) >> wfSigbody sl end
    | wfModtype (ModTypeFunctor (v, m1, m2)) =
      wfModtype m1 >> bindAbsMod v m1 (wfModtype m2)
  and wfSpec (SpecAbsMod m) = wfModtype m
    | wfSpec (SpecManifestMod (m1, m2)) =
      wfModtype m1 >> cModexpr m2 m1 >> return ()
    | wfSpec (SpecAbsTerm m) =
      whptTerm m >>= (fn m' => isSort m' >> return ())
    | wfSpec (SpecManifestTerm (m1, m2)) =
      whptTerm m2 >>= (fn m2' => Normalize.bequiv m1 m2')
  and cModexpr m m' =
    ptModexpr m >>= (fn m'' =>
    wfModtype m' >> subcModtype m'' m' >> return m')
  and ptModexpr m =
    qpModexpr m >>= (fn m' =>
    return (strModtype m m'))
  and qpModexpr (ModStruct dl) =
    let fun cbody ([]) = return ([])
      | cbody ((v, d)::dl') =
        (case d of
          DefVal m => ptTerm m >>= (fn m' =>
            return [(v, SpecManifestTerm (m', m))])
        | DefMod m => ptModexpr m >>= (fn m' =>
          return [(v, SpecAbsMod m')])
        | DefModSig (m1, m2) => 
          cModexpr m1 m2 >> return [((v, SpecAbsMod m2))]
        | DefModTransparent m => ptModexpr m >>= (fn m' =>
          return [(v, SpecManifestMod (m', m))])
        ) >>= (fn vsl =>
        bindMany vsl (cbody dl') >>= (fn sl =>
        return (vsl @ sl)))
    in cbody dl >>= (fn vsl =>
      allDiff (domain vsl) >> return (ModTypeSig vsl)) end
    | qpModexpr (ModFunctor (v, m1, m2)) =
      wfModtype m1 >> bindAbsMod v m1 (qpModexpr m2) >>= (fn m2' =>
      return (ModTypeFunctor (v, m1, m2')))
    | qpModexpr (ModApp (m1, m2)) =
      qpModexpr m1 >>= (fn m1' =>
      Term.isFuncT m1' >>= (fn (v, m1'', m2'') =>
      cModexpr m2 m1''>>= (fn m2' =>
      return (MSub.substModtype v m2 m2''))))
    | qpModexpr (ModPath p) =
      qpPath p >>= (fn s => getSpecModtype s)
  and cPath p s =
    wfSpec s >> ptPath p >>= (fn s' => subcSpec s s' >> return s)
  and ptPath p =
    qpPath p >>= (fn s => return (strSpec p s))
  and qpPath (PVar v) = getEntry v
    | qpPath (PPath (m, v)) =
      qpModexpr m >>= (fn s =>
      Term.isSig s >>= (fn s' =>
      field (PPath (m, v)) s'))
  and gammaRestr dom ([]) = return []
    | gammaRestr dom ((x, s)::xs) =
      if List.exists (fn v => eqv v x) dom then
        cPath (PVar x) s >>= (fn s' =>
        gammaRestr dom xs >>= (fn xs' =>
        return ((x, s')::xs')))
      else throw ()
  and subcModtype (ModTypeSig sl1) (ModTypeSig sl2) =
      bindMany sl1 (gammaRestr (domain sl1) sl2) >> return ()
    | subcModtype (ModTypeFunctor (v1, m1, m2))
                (ModTypeFunctor (v2, m1', m2')) =
      subcModtype m1' m1 >>
      bindAbsMod v1 m1' (subcModtype m2 m2') >> return ()
    | subcModtype _ _ = throw ()
  and subcSpec s (SpecAbsMod m') =
      getSpecModtype s >>= (fn s' => subcModtype s' m')
    | subcSpec (SpecManifestMod (m1, m2)) (SpecManifestMod (m1', m2')) =
      subcModtype m1 m1' >> Normalize.mequiv m2 m2'
    | subcSpec s (SpecAbsTerm m) =
      getSpecType s >>= (fn s' => Normalize.bequiv s' m)
    | subcSpec (SpecManifestTerm (m1, m2)) (SpecManifestTerm (m1', m2')) =
      Normalize.bequiv m1 m1' >> Normalize.bequiv m2 m2'
    | subcSpec _ _ = throw ()
  and cTerm t1 t2 =
    ptTerm t1 >>= (fn t1' => whptTerm t2 >>= (fn t2' =>
    isSort t2' >> Normalize.bequiv t2 t1'))
  and ptTerm (Path p) = qpPath p >>= (fn s => getSpecType s)
    | ptTerm (Lit (IntLit _)) = return (Lit (IntTyLit))
    | ptTerm (Lit (BoolLit _)) = return (Lit (BoolTyLit))
    | ptTerm (Lit (IntTyLit)) = return (Sort TypeVal)
    | ptTerm (Lit (BoolTyLit)) = return (Sort TypeVal)
    | ptTerm (Sort s) = hasAxiom s >>= (fn s' => return (Sort s'))
    | ptTerm (App (t1, t2)) =
      whptTerm t1 >>= (fn t1' =>
      Term.isDepProduct t1' >>= (fn (v, t3, t4) =>
      cTerm t2 t3 >> return (TSub.substTerm v t2 t4)))
    | ptTerm (Case (t1, t2, pml)) = raise Fail ""
(*
    TWO cases:
      t2 type is dep product leading to sort


      t2 type is nondepedent function of dep product args returning I applied to
      args, returning a sort

      *)
    | ptTerm (IfElse (t1, t2, t3)) =
      ptTerm t1 >>= (fn t1' =>
      whptTerm t2 >>= (fn t2' =>
      whptTerm t3 >>= (fn t3' =>
      Normalize.bequiv t2' t3' >>
      Term.isBoolTy t1' >> return t2')))
    | ptTerm (Let (v, t1, t2, t3)) =
      whptTerm t1 >>= (fn t1' => isSort t1' >>
      whptTerm t2 >>= (fn t2' =>
      Normalize.bequiv t1 t2' >>
      bindManifestTerm v t1 t2 (whptTerm t3) >>= (fn t3' =>
      return (Let (v, t1, t2, t3')))))
    | ptTerm (Lambda (v, t1, t2)) =
      whptTerm t1 >>= (fn t1' => isSort t1' >>
      bindAbsTerm v t1 (ptTerm t2) >>= (fn t2' =>
      ptTerm (DepProduct (v, t1, t2')) >>= (fn t3 =>
      isSort t3 >>
      return (DepProduct (v, t1, t2')))))
    | ptTerm (DepProduct (v, t1, t2)) =
      whptTerm t1 >>= (fn t1' => isSort t1' >>= (fn s1 =>
      bindAbsTerm v t1 (whptTerm t2) >>= (fn t2' =>
      isSort t2' >>= (fn s2 =>
      rho s1 s2 >>= (fn s3 => return (Sort s3))))))
    | ptTerm (Inductive ((v, t), tl)) =
      Term.arity t >>= (fn s =>
      let fun f ([]) = return ()
        | f (t'::tl') =
          bindAbsTerm v t (ptTerm t') >>= (fn t'' => isSort t'' >>= (fn s' =>
          if s = s' then Term.constructorForm v t' >> f tl'
          else throw ())) in f tl >> return t end)
    | ptTerm (Constr (i, t)) = 
      ptTerm t >>= (fn t' =>
      Term.isInductive t' >>= (fn (v, t, tl) =>
      ptTerm t' >>= (fn _ =>
      return (TSub.substTerm v t' (List.nth (tl, i))))))
  and whptTerm t =
    ptTerm t >>= (fn t' => Normalize.termreduce 
      Normalize.WeakHeadNormalForm t' >>= (fn t'' => return t''))

  and lrsub x i q r' c =
    let fun f r (DepProduct (AnonVar, m1, m2)) =
      newvar >>= (fn (v : MTS.var) =>
      f (App (r, Path (PVar v))) m2 >>= (fn m2' =>
      return (DepProduct (v, TSub.substTerm x i m1, m2'))))
      | f r (DepProduct (NamedVar v, m1, m2)) =
        f (App (r, Path (PVar (NamedVar v)))) m2 >>= (fn m2' =>
        return (DepProduct (NamedVar v, TSub.substTerm x i m1, m2')))
      | f r (App (m1, m2)) =
        f r m1 >>= (fn m1' => return (App (App (m1', m2), r)))
      | f r (Path (PVar v)) =
        if eqv x v then return q else throw ()
      | f r (Path (PPath (p, v))) = raise Fail ""
      | f _ _ = throw ()
    in f r' c end

  (* and lrsub x i q r (DepProduct (AnonVar, m1, m2)) =
    newvar >>= (fn v =>
      f i q (App (r, Path (PVar v))) m2 >>= (fn m2' =>
      return (DepProduct (v, TSub.substTerm x i m1, m2'))))
    
    | lrsub x i q r (DepProduct (NamedVar v, m1, m2)) =
      lrsub x i q (App (r, Path (PVar v))) >>= (fn m2' =>
        return (DepProduct (v, TSub.substTerm x i m1, m2')))
    | lrsub x i q (App (m1, m2)) =
      lrsub x i q m1 >>= (fn m1' => return (App (m1', m2)))
    | lrsub x i q (Path (PVar v)) =
      if eqv x v then return q else throw ()
    | lrsub x i q (Path (PPath (p, v))) = raise Fail ""
    *)
end
