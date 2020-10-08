structure MTSCheck : sig
  include MONAD
  datatype enventry =
    EnvTy of MTS.var * MTS.term
  | EnvDel of MTS.var * MTS.term * MTS.term
  type env = enventry list

  val registerSort : MTS.sort -> unit monad
  val registerAxiom : MTS.sort -> MTS.sort -> unit monad
  val registerRule : MTS.sort -> MTS.sort -> MTS.sort -> unit monad

  val isSort : MTS.term -> MTS.sort monad
  val isBottomSort : MTS.sort -> unit monad
  val isTopSort : MTS.sort -> unit monad
  val hasAxiom : MTS.sort -> MTS.sort monad
  val hasRule : MTS.sort -> MTS.sort -> MTS.sort monad
  val startsRule : MTS.sort -> unit monad

  val inEnv : MTS.var -> env -> bool
  val isFresh : MTS.var -> unit monad
  val bindTy : MTS.var -> MTS.term -> 'a monad -> 'a monad
  val bindDel : MTS.var -> MTS.term -> MTS.term -> 'a monad -> 'a monad

  val plus : MTS.sort -> MTS.sort monad
  val minus : MTS.sort -> MTS.sort monad
  val rho : MTS.sort -> MTS.sort -> MTS.sort monad
  val mu : MTS.sort -> MTS.sort -> MTS.sort monad
  val elmtclass : MTS.term -> MTS.sort monad
  val sortclass : MTS.term -> MTS.sort monad

  val subst : MTS.var -> MTS.term -> MTS.term -> MTS.term monad
  val nfstep : MTS.term -> MTS.term monad
  val nfreduce : MTS.term -> MTS.term monad

  val whsdcl : MTS.term -> MTS.term monad
  val sdcl : MTS.term -> MTS.term monad

  (* val classTyForm : MTS.term -> MTS.sort monad
  val classConForm : MTS.term -> MTS.var monad *)

  val checkVal : MTS.valdef -> MTS.sort monad
  val checkData : MTS.datadef -> MTS.sort monad
  val checkNewTy : MTS.newtydef -> MTS.sort monad
  val checkClass : MTS.classdef -> MTS.sort monad
  val checkInstance : MTS.instancedef -> MTS.sort monad
end
=
struct
  datatype enventry =
    EnvTy of MTS.var * MTS.term
  | EnvDel of MTS.var * MTS.term * MTS.term
  type env = enventry list
  type s = MTS.sorts * MTS.ax * MTS.rules
  structure M = StateFunctor (type s = s)
  structure MM = ReaderT (type s = env; structure M = M)
  structure MMM = OptionT (structure M = MM)
  structure Util = MUtil (structure M = MMM)
  open MMM
  open MTS

  val getstate = lift (MM.lift M.get)

  val putstate = (fn st => lift (MM.lift (M.put st)))

  val ask = lift MM.ask

  fun loc f m = (MM.loc f) m

  fun registerSort srt =
    getstate >>= (fn (srts, axs, rls) =>
    putstate (srt::srts, axs, rls))

  fun registerAxiom s1 s2 =
    getstate >>= (fn (srts, axs, rls) =>
    putstate (srts, (s1, s2)::axs, rls))

  fun registerRule s1 s2 s3 =
    getstate >>= (fn (srts, axs, rls) =>
    putstate (srts, axs, (s1, s2, s3)::rls))

  fun isSort (Sort s) =
    getstate >>= (fn (srts, axs, rls) =>
      if List.exists (fn x => x = s) srts
      then return s else zero ())
  | isSort _ = zero ()

  fun isBottomSort srt =
    getstate >>= (fn (srts, axs, rls) =>
      if List.exists (fn (s1, s2) => s2 = srt) axs
      then zero () else return ())

  fun isTopSort srt =
    getstate >>= (fn (srts, axs, rls) =>
      if List.exists (fn (s1, s2) => s1 = srt) axs
      then zero () else return ())

  fun hasAxiom s1 =
    getstate >>= (fn (srts, axs, rls) =>
      (case List.find (fn (s1', s2) => s1 = s1') axs of
        SOME (s1, s2) => return s2
      | NONE => zero ()))

  fun hasRule s1 s2 =
    getstate >>= (fn (srts, axs, rls) =>
      (case List.find (fn (s1', s2', s3) => s1 = s1' andalso s2 = s2') rls of
        SOME (s1, s2, s3) => return s3
      | NONE => zero ()))

  fun startsRule s1 =
    getstate >>= (fn (srts, axs, rls) =>
      (case List.find (fn (s1', s2', s3) => s1 = s1') rls of
        SOME (s1, s2, s3) => return ()
      | NONE => zero ()))

  fun inEnv v e =
    List.exists (fn x => (case x of
        EnvTy (v', m) => v = v'
      | EnvDel (v', m1, m2) => v = v')) e

  fun isFresh v =
    ask >>= (fn e =>
    if inEnv v e then zero ()
    else return ())

  fun bindTy v m =
    loc (fn e => (EnvTy (v, m))::e)

  fun bindDel v m1 m2 =
    loc (fn e => (EnvDel (v, m1, m2))::e)

  fun getTy v =
    ask >>= (fn e =>
      case List.find (fn x => (case x of
          EnvTy (v', m) => v = v'
        | EnvDel (v', m1, m2) => v = v')) e of
        SOME (EnvTy (_, m)) => return m
      | SOME (EnvDel (_, m, _)) => return m
      | NONE => zero ())

  fun trimEnv v =
    let
      fun f (e0) ([]) = raise Fail "should not happen if you checked"
      | f (e0) (e::e1) =
        (case e of
          EnvTy (v', m) =>
            if eqv v v' then List.rev e0
            else f (e::e0) e1
        | EnvDel (v', m1, m2) =>
            if eqv v v' then List.rev e0
            else f (e::e0) e1)
    in
      loc (f [])
    end

  fun isLambda (Lambda (v, m1, m2)) = return (v, m1, m2)
  | isLambda _ = zero ()

  fun isDepProduct (DepProduct (v, m1, m2)) = return (v, m1, m2)
  | isDepProduct _ = zero ()

  fun isDepSum (DepSum (v, m1, m2)) = return (v, m1, m2)
  | isDepSum _ = zero ()

  fun isBoolTy (Lit BoolTyLit) = return ()
  | isBoolTy _ = zero ()

  fun plus s1 =
    getstate >>= (fn (srts, axs, rls) =>
      (case List.find (fn (s1', s2) => s1 = s1') axs of
        SOME (s1, s2) => return s2
      | NONE => zero ()))

  fun minus s2 =
    getstate >>= (fn (srts, axs, rls) =>
      (case List.find (fn (s1, s2') => s2 = s2') axs of
        SOME (s1, s2) => return s1
      | NONE => zero ()))

  fun rho s1 s2 =
    getstate >>= (fn (srts, axs, rls) =>
      (case List.find (fn (s1', s2', s3) => s1 = s1' andalso s2 = s2') rls of
        SOME (s1, s2, s3) => return s3
      | NONE => zero ()))

  fun mu s1 s2 =
    getstate >>= (fn (srts, axs, rls) =>
      (case List.find (fn (s1', s3, s2') => s1 = s1' andalso s2 = s2') rls of
        SOME (_, s3, _) => return s3
      | NONE => zero ()))

  and elmtclass (Var v) =
      getTy v >>= (fn m =>
      trimEnv v (sortclass m))
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
      bindDel v m1 m2 (elmtclass m3)
  | elmtclass (Lambda (v, m1, m2)) =
      elmtclass m1 >>= (fn s1 =>
      bindTy v m1 (elmtclass m2) >>= (fn s2 => rho s1 s2))
  | elmtclass (DepProduct (v, m1, m2)) =
      sortclass (DepProduct (v, m1, m2)) >>= plus
  | elmtclass (DepSum (v, m1, m2)) =
      sortclass (DepSum (v, m1, m2)) >>= plus
  | elmtclass (Tuple (m1, m2, m3)) = raise Fail ""
  | elmtclass (First m) = raise Fail ""
  | elmtclass (Second m) = raise Fail ""

  and sortclass (Var v) = elmtclass (Var v) >>= minus
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
      bindDel v m1 m2 (sortclass m3)
  | sortclass (Lambda (v, m1, m2)) =
      elmtclass (Lambda (v, m1, m2)) >>= minus
  | sortclass (DepProduct (v, m1, m2)) =
      sortclass m1 >>= (fn s1 =>
      bindTy v m1 (sortclass m2) >>= (fn s2 => rho s1 s2))
  | sortclass (DepSum (v, m1, m2)) =
      sortclass m1 >>= (fn s1 =>
      bindTy v m1 (sortclass m2) >>= (fn s2 => rho s1 s2))
  | sortclass (Tuple (m1, m2, m3)) = raise Fail ""
  | sortclass (First m) = raise Fail ""
  | sortclass (Second m) = raise Fail ""

  fun subst x x' (Var v) =
      if v = x then return (Var v) else return (Var v)
  | subst x x' (Lit l) = return (Lit l)
  | subst x x' (Sort s) = return (Sort s)
  | subst x x' (App (m1, m2)) =
      (subst x x' m1 >>= (fn m1' =>
      (subst x x' m2 >>= (fn m2' =>
        return (App (m1', m2'))))))
  | subst x x' (Case (m1, pml, m2)) = raise Fail ""
  | subst x x' (IfElse (m1, m2, m3)) =
      (subst x x' m1 >>= (fn m1' =>
      (subst x x' m2 >>= (fn m2' =>
      (subst x x' m3 >>= (fn m3' =>
        return (IfElse (m1', m2', m3'))))))))
  | subst x x' (Let (v, m1, m2, m3)) =
      (subst x x' m1 >>= (fn m1' =>
      (subst x x' m2 >>= (fn m2' =>
      (subst x x' m3 >>= (fn m3' =>
        return (Let (v, m1', m2', m3'))))))))
  | subst x x' (Lambda (v, m1, m2)) =
      (subst x x' m1 >>= (fn m1' =>
      (subst x x' m2 >>= (fn m2' =>
        return (Lambda (v, m1', m2'))))))
  | subst x x' (DepProduct (v, m1, m2)) =
      (subst x x' m1 >>= (fn m1' =>
      (subst x x' m2 >>= (fn m2' =>
        return (DepProduct (v, m1', m2'))))))
  | subst x x' (DepSum (v, m1, m2)) =
      (subst x x' m1 >>= (fn m1' =>
      (subst x x' m2 >>= (fn m2' =>
        return (DepSum (v, m1', m2'))))))
  | subst x x' (Tuple (m1, m2, m3)) =
      (subst x x' m1 >>= (fn m1' =>
      (subst x x' m2 >>= (fn m2' =>
      (subst x x' m3 >>= (fn m3' =>
        return (Tuple (m1', m2', m3'))))))))
  | subst x x' (First m) =
      (subst x x' m >>= (fn m' =>
        return (First m')))
  | subst x x' (Second m) =
      (subst x x' m >>= (fn m' =>
        return (Second m')))

  fun nfstep (Var _) = zero ()
  | nfstep (Lit _) = zero ()
  | nfstep (Sort _) = zero ()
  | nfstep (App (m1, m2)) =
      (nfstep m1 >>= (fn m1' => return (App (m1', m2))))
      ++ (nfstep m2 >>= (fn m2' => return (App (m1, m2'))))
      ++ (isLambda m1 >>= (fn (v, m3, m4) => subst v m2 m4))
  | nfstep (Case (m1, pml, m2)) = raise Fail ""
  | nfstep (IfElse (m1, m2, m3)) =
      (nfstep m1 >>= (fn m1' => return (IfElse (m1', m2, m3))))
      ++ (nfstep m2 >>= (fn m2' => return (IfElse (m1, m2', m3))))
      ++ (nfstep m3 >>= (fn m3' => return (IfElse (m1, m2, m3'))))
  | nfstep (Let (v, m1, m2, m3)) =
      (nfstep m1 >>= (fn m1' => return (Let (v, m1', m2, m3))))
      ++ (nfstep m2 >>= (fn m2' => return (Let (v, m1, m2', m3))))
      ++ (nfstep m3 >>= (fn m3' => return (Let (v, m1, m2, m3'))))
  | nfstep (Lambda (v, m1, m2)) =
      (nfstep m1 >>= (fn m1' => return (Lambda (v, m1', m2))))
      ++ (nfstep m2 >>= (fn m2' => return (Lambda (v, m1, m2'))))
  | nfstep (DepProduct (v, m1, m2)) =
      (nfstep m1 >>= (fn m1' => return (DepProduct (v, m1', m2))))
      ++ (nfstep m2 >>= (fn m2' => return (DepProduct (v, m1, m2'))))
  | nfstep (DepSum (v, m1, m2)) = raise Fail ""
  | nfstep (Tuple (m1, m2, m3)) = raise Fail ""
  | nfstep (First m) = raise Fail ""
  | nfstep (Second m) = raise Fail ""

  fun nfreduce m =
    (nfstep m >>= (fn m' => nfreduce m')) ++ return m

  fun whstep (Var _) = zero ()
  | whstep (Lit _) = zero ()
  | whstep (Sort _) = zero ()
  | whstep (App (m1, m2)) =
      (whstep m1 >>= (fn m1' => return (App (m1', m2))))
      ++ (isLambda m1 >>= (fn (v, m3, m4) => subst v m2 m4))
  | whstep (Case (m1, pml, m2)) = raise Fail ""
  | whstep (IfElse (m1, m2, m3)) =
      (whstep m1 >>= (fn m1' => return (IfElse (m1', m2, m3))))
      ++ (whstep m2 >>= (fn m2' => return (IfElse (m1, m2', m3))))
      ++ (whstep m3 >>= (fn m3' => return (IfElse (m1, m2, m3'))))
  | whstep (Let (v, m1, m2, m3)) =
      (whstep m1 >>= (fn m1' => return (Let (v, m1', m2, m3))))
      ++ (whstep m2 >>= (fn m2' => return (Let (v, m1, m2', m3))))
      ++ (whstep m3 >>= (fn m3' => return (Let (v, m1, m2, m3'))))
  | whstep (Lambda (v, m1, m2)) =
      (whstep m1 >>= (fn m1' => return (Lambda (v, m1', m2))))
      ++ (whstep m2 >>= (fn m2' => return (Lambda (v, m1, m2'))))
  | whstep (DepProduct (v, m1, m2)) =
      (whstep m1 >>= (fn m1' => return (DepProduct (v, m1', m2))))
      ++ (whstep m2 >>= (fn m2' => return (DepProduct (v, m1, m2'))))
  | whstep (DepSum (v, m1, m2)) = raise Fail ""
  | whstep (Tuple (m1, m2, m3)) = raise Fail ""
  | whstep (First m) = raise Fail ""
  | whstep (Second m) = raise Fail ""

  fun whreduce m =
    (whstep m >>= (fn m' => whreduce m')) ++ return m

  fun bequiv m1 m2 =
    nfreduce m1 >>= (fn m1' =>
    nfreduce m2 >>= (fn m2' =>
      if eq m1' m2' then return ()
      else zero ()))

  fun whsdcl m =
    sdcl m >>= (fn m' => whreduce m' >>= (fn m'' => return m''))
  and sdcl (Var v) =
      getTy v >>= (fn m =>
      whsdcl m >>= (fn m' =>
      isSort m' >>= (fn _ =>
      return m)))
  | sdcl (Lit (IntLit _)) = return (Lit (IntTyLit))
  | sdcl (Lit (BoolLit _)) = return (Lit (BoolTyLit))
  | sdcl (Lit (IntTyLit)) = return (Sort TypeVal)
  | sdcl (Lit (BoolTyLit)) = return (Sort TypeVal)
  | sdcl (Sort s) = hasAxiom s >>= (fn s' => return (Sort s'))
  | sdcl (App (m1, m2)) =
      whsdcl m1 >>= (fn m1' =>
      sdcl m2 >>= (fn m2' =>
      isDepProduct m2' >>= (fn (v, m1'', m2'') => subst v m2 m2'')))
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
      bindDel v m1 m2 (whsdcl m3) >>= (fn m3' =>
      return (Let (v, m1, m2, m3')))))))
  | sdcl (Lambda (v, m1, m2)) =
      elmtclass (Lambda (v, m1, m2)) >>= (fn _ =>
      bindTy v m1 (sdcl m2) >>= (fn m2' =>
      return (DepProduct (v, m1, m2'))))
  | sdcl (DepProduct (v, m1, m2)) =
      sortclass m1 >>= (fn s1 =>
      bindTy v m1 (whsdcl m2 >>= (fn m2' => isSort m2')) >>= (fn s2 =>
      rho s1 s2 >>= (fn s3 => return (Sort s3))))
  | sdcl (DepSum (v, m1, m2)) = raise Fail ""
  | sdcl (Tuple (m1, m2, m3)) = raise Fail ""
  | sdcl (First m) = raise Fail ""
  | sdcl (Second m) = raise Fail ""

  fun checkVal (v, m1, m2) = raise Fail ""
  fun checkData (tname, tm, dcml) = raise Fail ""
  fun checkNewTy (cname, cm) = raise Fail ""
  fun checkClass (clname, cml) = raise Fail ""
  fun checkInstance (clname, iname, cml) = raise Fail ""

end

