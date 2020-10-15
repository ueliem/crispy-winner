structure InterpM : sig
  include MONADZEROPLUS
  datatype enventry =
    EnvTy of MTS.var * MTS.term
  | EnvDel of MTS.var * MTS.term * MTS.term
  | EnvSpec of MTS.var * MTS.specification
  type env = enventry list
  type s = MTS.sorts * MTS.ax * MTS.rules

  val getstate : s monad
  val putstate : s -> unit monad
  val ask : env monad
  val loc : (env -> env) -> 'a monad -> 'a monad

  val inEnv : MTS.var -> env -> bool
  val isFresh : MTS.var -> unit monad
  val trimEnv : MTS.var -> 'a monad -> 'a monad
  val bindTy : MTS.var -> MTS.term -> 'a monad -> 'a monad
  val bindDel : MTS.var -> MTS.term -> MTS.term -> 'a monad -> 'a monad

  val registerSort : MTS.sort -> unit monad
  val registerAxiom : MTS.sort -> MTS.sort -> unit monad
  val registerRule : MTS.sort -> MTS.sort -> MTS.sort -> unit monad
  
  val getSorts : unit -> MTS.sorts monad
  val getAxioms : unit -> MTS.ax monad
  val getRules : unit -> MTS.rules monad

  val getTy : MTS.var -> MTS.term monad
  val isLambda : MTS.term -> (MTS.var * MTS.term * MTS.term) monad
  val isDepProduct : MTS.term -> (MTS.var * MTS.term * MTS.term) monad
  val isBoolTy : MTS.term -> unit monad

  val subst : MTS.var -> MTS.term -> MTS.term -> MTS.term monad
  val whstep : MTS.term -> MTS.term monad
  val whreduce : MTS.term -> MTS.term monad
  val nfstep : MTS.term -> MTS.term monad
  val nfreduce : MTS.term -> MTS.term monad
  val bequiv : MTS.term -> MTS.term -> unit monad

end
=
struct
  datatype enventry =
    EnvTy of MTS.var * MTS.term
  | EnvDel of MTS.var * MTS.term * MTS.term
  | EnvSpec of MTS.var * MTS.specification
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

  fun getSorts () =
    getstate >>= (fn (srts, axs, rls) => return srts)

  fun getAxioms () =
    getstate >>= (fn (srts, axs, rls) => return axs)

  fun getRules () =
    getstate >>= (fn (srts, axs, rls) => return rls)

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

  fun isBoolTy (Lit BoolTyLit) = return ()
  | isBoolTy _ = zero ()

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

  fun whreduce m =
    (whstep m >>= (fn m' => whreduce m')) ++ return m

  fun bequiv m1 m2 =
    nfreduce m1 >>= (fn m1' =>
    nfreduce m2 >>= (fn m2' =>
      if eq m1' m2' then return ()
      else zero ()))

end


