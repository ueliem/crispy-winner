structure Normalize : sig
  type strategy = {
    inside : bool, args : bool, beta : bool, betaMod : bool,
    rho : bool, delta : bool, iota : bool, fix : bool }
  val shouldReduceUnderAbs : strategy -> bool
  val shouldReduceArgs : strategy -> bool
  val shouldBetaReduce : strategy -> bool
  val shouldBetaModReduce : strategy -> bool
  val shouldFieldSelect : strategy -> bool
  val shouldManifestFieldReduce : strategy -> bool
  val shouldMatchOnConstr : strategy -> bool
  val shouldFixReduce : strategy -> bool
  val normalFormStrat : strategy 
  val weakNormalFormStrat : strategy 
  val headNormalFormStrat : strategy 
  val weakHeadNormalFormStrat : strategy 
  type 'a monad = 'a MTSInterpM.monad
  val pathstep : strategy -> MTS.path -> MTS.path monad
  val termstep : strategy -> MTS.term -> MTS.term monad
  val termreduce : strategy -> MTS.term -> MTS.term monad
  val mexprstep : strategy -> MTS.modexpr -> MTS.modexpr monad
  val mexprreduce : strategy -> MTS.modexpr -> MTS.modexpr monad
  val termNormalForm : MTS.term -> MTS.term monad
  val termWeakNormalForm : MTS.term -> MTS.term monad
  val termHeadNormalForm : MTS.term -> MTS.term monad
  val termWeakHeadNormalForm : MTS.term -> MTS.term monad
  val mexprNormalForm : MTS.modexpr -> MTS.modexpr monad
  val mexprWeakNormalForm : MTS.modexpr -> MTS.modexpr monad
  val mexprHeadNormalForm : MTS.modexpr -> MTS.modexpr monad
  val mexprWeakHeadNormalForm : MTS.modexpr -> MTS.modexpr monad
  val bequiv : MTS.term -> MTS.term -> unit monad
  val mequiv : MTS.modexpr -> MTS.modexpr -> unit monad
end = struct
  type strategy = {
    inside : bool, args : bool, beta : bool, betaMod : bool,
    rho : bool, delta : bool, iota : bool, fix : bool }
  fun shouldReduceUnderAbs ({ inside, args, beta, betaMod,
                              rho, delta, iota, fix }) = inside
  fun shouldReduceArgs ({ inside, args, beta, betaMod,
                          rho, delta, iota, fix }) = args
  fun shouldBetaReduce ({ inside, args, beta, betaMod,
                          rho, delta, iota, fix }) = beta
  fun shouldBetaModReduce ({ inside, args, beta, betaMod,
                             rho, delta, iota, fix }) = betaMod
  fun shouldFieldSelect ({ inside, args, beta, betaMod,
                           rho, delta, iota, fix }) = rho
  fun shouldManifestFieldReduce ({ inside, args, beta, betaMod,
                                   rho, delta, iota, fix }) = delta
  fun shouldMatchOnConstr ({ inside, args, beta, betaMod,
                             rho, delta, iota, fix }) = iota
  fun shouldFixReduce ({ inside, args, beta, betaMod,
                         rho, delta, iota, fix }) = fix
  val normalFormStrat = {
    inside = true, args = true, beta = true, betaMod = true,
    rho = true, delta = true, iota = true, fix = false }
  val weakNormalFormStrat = {
    inside = false, args = true, beta = true, betaMod = true,
    rho = true, delta = true, iota = true, fix = false }
  val headNormalFormStrat = {
    inside = true, args = false, beta = true, betaMod = true,
    rho = true, delta = true, iota = true, fix = false }
  val weakHeadNormalFormStrat = {
    inside = false, args = false, beta = true, betaMod = true,
    rho = true, delta = true, iota = true, fix = false }
  type 'a monad = 'a MTSInterpM.monad
  open MTS
  open MTSInterpM
  fun pathstep str (PPath (p, v)) =
    (mexprstep str p >>= (fn p' => return (PPath (p', v)))) ++ zero ()
    | pathstep str (PVar v) = zero ()
  and termstep str (Path p) = (pathstep str p >>= (fn p' => return (Path p')))
    ++ (if shouldFieldSelect str then Term.structDef p >>= (fn d =>
      getDefTerm d >>= (fn t => return t)) else zero ())
    ++ (if shouldManifestFieldReduce str then 
      PseudoType.pseudoSpec p >>= (fn s => getSpecTerm s) else zero ())
    | termstep str (Lit _) = zero ()
    | termstep str (Sort _) = zero ()
    | termstep str (App (m1, m2)) =
      (termstep str m1 >>= (fn m1' => return (App (m1', m2))))
      ++ (if shouldReduceArgs str then termstep str m2 >>= (fn m2' =>
        return (App (m1, m2'))) else zero ())
      ++ (if shouldBetaReduce str then Term.isLambda m1 >>= (fn (v, m3, m4) =>
        return (TSub.substTerm v m2 m4)) else zero ())
    (* | termstep str (Case (m1, m2, ml)) =
      (termstep str m1 >>= (fn m1' => return (Case (m1', m2, ml))))
      ++ (return (raise Fail "")) *)
    | termstep str (IfElse (m1, m2, m3)) =
      (termstep str m1 >>= (fn m1' => return (IfElse (m1', m2, m3))))
      ++ (termstep str m2 >>= (fn m2' => return (IfElse (m1, m2', m3))))
      ++ (termstep str m3 >>= (fn m3' => return (IfElse (m1, m2, m3'))))
    | termstep str (Let (v, m1, m2, m3)) =
      (termstep str m1 >>= (fn m1' => return (Let (v, m1', m2, m3))))
      ++ (termstep str m2 >>= (fn m2' => return (Let (v, m1, m2', m3))))
      ++ (termstep str m3 >>= (fn m3' => return (Let (v, m1, m2, m3'))))
    | termstep str (Lambda (v, m1, m2)) =
      (if shouldReduceUnderAbs str then termstep str m2 >>= (fn m2' =>
        return (Lambda (v, m1, m2'))) else zero ())
    | termstep str (DepProduct (v, m1, m2)) =
      (termstep str m1 >>= (fn m1' => return (DepProduct (v, m1', m2))))
      ++ (termstep str m2 >>= (fn m2' => return (DepProduct (v, m1, m2'))))
    | termstep str (Fix (v, m1, m2)) = (if shouldFixReduce str then
      return (App (Lambda (v, m1, m2), Fix (v, m1, m2))) else zero ())
    | termstep str (Inductive ((v, t), tl)) = zero ()
    | termstep str (Constr (i, t)) =
      (termstep str t >>= (fn t' => return (Constr (i, t')))) ++ zero ()
  and mexprstep str (ModStruct dl) = zero ()
    | mexprstep str (ModFunctor (v, m1, m2)) = zero ()
    | mexprstep str (ModApp (m1, m2)) =
      (mexprstep str m1 >>= (fn m1' => return (ModApp (m1', m2))))
      ++ (if shouldBetaModReduce str then Term.isFunctor m1 >>= (fn (v, m3, m4) =>
        return (MSub.substModexpr v m2 m4)) else zero ())
    | mexprstep str (ModPath p) =
      (pathstep str p >>= (fn p' => return (ModPath p')))
      ++ (if shouldFieldSelect str then Term.structDef p >>= (fn d =>
        getDefModexpr d >>= (fn m => return m)) else zero ())
      ++ (if shouldManifestFieldReduce str then
        PseudoType.pseudoSpec p >>= (fn s => getSpecModexpr s) else zero ())
  fun termreduce str m =
    (termstep str m >>= (fn m' => termreduce str m')) ++ return m
  fun mexprreduce str m =
    (mexprstep str m >>= (fn m' => mexprreduce str m')) ++ return m
  val termNormalForm = termreduce normalFormStrat
  val termWeakNormalForm = termreduce weakNormalFormStrat
  val termHeadNormalForm = termreduce headNormalFormStrat
  val termWeakHeadNormalForm = termreduce weakHeadNormalFormStrat
  val mexprNormalForm = mexprreduce normalFormStrat
  val mexprWeakNormalForm = mexprreduce weakNormalFormStrat
  val mexprHeadNormalForm = mexprreduce headNormalFormStrat
  val mexprWeakHeadNormalForm = mexprreduce weakHeadNormalFormStrat
  fun bequiv m1 m2 =
    termreduce normalFormStrat m1 >>= (fn m1' =>
    termreduce normalFormStrat m2 >>= (fn m2' =>
      if Equiv.eq m1' m2' then return () else throw ()))
  fun mequiv m1 m2 =
    mexprreduce normalFormStrat m1 >>= (fn m1' =>
    mexprreduce normalFormStrat m2 >>= (fn m2' =>
      if Equiv.mexpreq m1' m2' then return ()
      else throw ()))
end
