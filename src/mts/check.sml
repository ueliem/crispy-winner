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

  (* val iiiisFresh : MTS.var -> unit monad *)
  val bindTy : MTS.var -> MTS.term -> unit monad
  val bindDel : MTS.var -> MTS.term -> MTS.term -> unit monad

  val isFresh : MTS.var -> env -> unit monad
  val inEnv : MTS.var -> env -> (env * enventry) monad
  val envWithTy : MTS.var -> MTS.term -> env -> env monad
  val envWithDel : MTS.var -> MTS.term -> MTS.term -> env -> env monad

  (* val classTyForm : MTS.term -> MTS.sort monad
  val classConForm : MTS.term -> MTS.var monad *)

  val plus : MTS.sort -> MTS.sort monad
  val minus : MTS.sort -> MTS.sort monad
  val rho : MTS.sort -> MTS.sort -> MTS.sort monad
  val mu : MTS.sort -> MTS.sort -> MTS.sort monad
  val elmtclass : env -> MTS.term -> MTS.sort monad
  val sortclass : env -> MTS.term -> MTS.sort monad

  val subst : MTS.var -> MTS.term -> MTS.term -> MTS.term monad
  val nfstep : MTS.term -> MTS.term monad
  val nfreduce : MTS.term -> MTS.term monad

  val whsdcl : env -> MTS.term -> MTS.term monad
  val sdcl : env -> MTS.term -> MTS.term monad

  val checkVal : env -> MTS.valdef -> (env * MTS.sort) monad
  val checkData : env -> MTS.datadef -> (env * MTS.sort) monad
  val checkNewTy : env -> MTS.newtydef -> (env * MTS.sort) monad
  val checkClass : env -> MTS.classdef -> (env * MTS.sort) monad
  val checkInstance : env -> MTS.instancedef -> (env * MTS.sort) monad
end
=
struct
  datatype enventry =
    EnvTy of MTS.var * MTS.term
  | EnvDel of MTS.var * MTS.term * MTS.term
  type env = enventry list
  type s = env * MTS.sorts * MTS.ax * MTS.rules
  structure M = StateFunctor (type s = s)
  structure MM = OptionT (structure M = M)
  open MM
  open MTS

  fun registerSort srt =
    lift M.get >>= (fn (e, srts, axs, rls) =>
    lift (M.put (e, srt::srts, axs, rls)))

  fun registerAxiom s1 s2 =
    lift M.get >>= (fn (e, srts, axs, rls) =>
    lift (M.put (e, srts, (s1, s2)::axs, rls)))

  fun registerRule s1 s2 s3 =
    lift M.get >>= (fn (e, srts, axs, rls) =>
    lift (M.put (e, srts, axs, (s1, s2, s3)::rls)))

  fun isSort (Sort s) =
    lift M.get >>= (fn (e, srts, axs, rls) =>
      if List.exists (fn x => x = s) srts
      then return s else zero ())
  | isSort _ = zero ()

  fun isBottomSort srt =
    lift M.get >>= (fn (e, srts, axs, rls) =>
      if List.exists (fn (s1, s2) => s2 = srt) axs
      then zero () else return ())

  fun isTopSort srt =
    lift M.get >>= (fn (e, srts, axs, rls) =>
      if List.exists (fn (s1, s2) => s1 = srt) axs
      then zero () else return ())

  fun hasAxiom s1 =
    lift M.get >>= (fn (e, srts, axs, rls) =>
      (case List.find (fn (s1', s2) => s1 = s1') axs of
        SOME (s1, s2) => return s2
      | NONE => zero ()))

  fun hasRule s1 s2 =
    lift M.get >>= (fn (e, srts, axs, rls) =>
      (case List.find (fn (s1', s2', s3) => s1 = s1' andalso s2 = s2') rls of
        SOME (s1, s2, s3) => return s3
      | NONE => zero ()))

  fun startsRule s1 =
    lift M.get >>= (fn (e, srts, axs, rls) =>
      (case List.find (fn (s1', s2', s3) => s1 = s1') rls of
        SOME (s1, s2, s3) => return ()
      | NONE => zero ()))

  fun bindTy v m =
    isFresh v e >>= (fn _ => return ((EnvTy (v, m))::e))

  fun bindDel v m1 m2 =
    isFresh v e >>= (fn _ =>
    lift M.get >>= (fn (e, srts, axs, rls) =>
    lift (M.put ((EnvDel (v, m1, m2))::e, srts, axs, rls)) >>= (fn _ =>
    return ()
    )))
  fun inEnv v e =
    let
      fun f (e0) ([]) = zero ()
      | f (e0) (e::e1) =
        (case e of
          EnvTy (v', m) =>
            if eqv v v' then return (List.rev e0, EnvTy (v', m))
            else f (e::e0) e1
        | EnvDel (v', m1, m2) =>
            if eqv v v' then return (List.rev e0, EnvDel (v', m1, m2))
            else f (e::e0) e1)
    in
      f [] e
    end

  fun isFresh v e =
    if List.exists (fn x => (case x of
        EnvTy (v', m) => v = v'
      | EnvDel (v', m1, m2) => v = v')) e then zero ()
    else return ()

  fun envWithTy v m e =
    isFresh v e >>= (fn _ => return ((EnvTy (v, m))::e))

  fun envWithDel v m1 m2 e =
    isFresh v e >>= (fn _ => return ((EnvDel (v, m1, m2))::e))

  fun plus s1 =
    lift M.get >>= (fn (e, srts, axs, rls) =>
      (case List.find (fn (s1', s2) => s1 = s1') axs of
        SOME (s1, s2) => return s2
      | NONE => zero ()))

  fun minus s2 =
    lift M.get >>= (fn (e, srts, axs, rls) =>
      (case List.find (fn (s1, s2') => s2 = s2') axs of
        SOME (s1, s2) => return s1
      | NONE => zero ()))

  fun rho s1 s2 =
    lift M.get >>= (fn (e, srts, axs, rls) =>
      (case List.find (fn (s1', s2', s3) => s1 = s1' andalso s2 = s2') rls of
        SOME (s1, s2, s3) => return s3
      | NONE => zero ()))

  fun mu s1 s2 =
    lift M.get >>= (fn (e, srts, axs, rls) =>
      (case List.find (fn (s1', s3, s2') => s1 = s1' andalso s2 = s2') rls of
        SOME (_, s3, _) => return s3
      | NONE => zero ()))

  and elmtclass e (Var v) =
      inEnv v e >>= (fn (e', m) =>
        (case m of
          EnvTy (v', m') => sortclass e' m'
        | EnvDel (v', m1, m2) => sortclass e' m1))
  | elmtclass e (Lit (IntLit _)) = return TypeVal
  | elmtclass e (Lit (IntTyLit)) = return KindVal
  | elmtclass e (Lit (BoolLit _)) = return TypeVal
  | elmtclass e (Lit (BoolTyLit)) = return KindVal
  | elmtclass e (Sort s) =
      sortclass e (Sort s) >>= plus
  | elmtclass e (App (m1, m2)) =
      elmtclass e m1 >>= (fn s1 =>
      elmtclass e m2 >>= (fn s2 => mu s1 s2))
  | elmtclass e (Case (m1, pml, m2)) = raise Fail ""
  | elmtclass e (IfElse (m1, m2, m3)) =
      elmtclass e m2 >>= (fn s2 =>
      elmtclass e m3 >>= (fn s3 =>
        if s2 = s3 then return s2 else zero ()
      ))
  | elmtclass e (Let (v, m1, m2, m3)) =
      envWithDel v m1 m2 e >>= (fn e' => elmtclass e' m3)
  | elmtclass e (Lambda (v, m1, m2)) =
      elmtclass e m1 >>= (fn s1 =>
      envWithTy v m1 e >>= (fn e' =>
      elmtclass e' m2 >>= (fn s2 => rho s1 s2)))
  | elmtclass e (DepProduct (v, m1, m2)) =
      sortclass e (DepProduct (v, m1, m2)) >>= plus
  | elmtclass e (DepSum (v, m1, m2)) =
      sortclass e (DepSum (v, m1, m2)) >>= plus
  | elmtclass e (Tuple (m1, m2, m3)) = raise Fail ""
  | elmtclass e (First m) = raise Fail ""
  | elmtclass e (Second m) = raise Fail ""

  and sortclass e (Var v) = elmtclass e (Var v) >>= minus
  | sortclass e (Lit (IntLit _)) = zero ()
  | sortclass e (Lit (IntTyLit)) = return TypeVal
  | sortclass e (Lit (BoolLit _)) = zero ()
  | sortclass e (Lit (BoolTyLit)) = return TypeVal
  | sortclass e (Sort s) = plus s
  | sortclass e (App (m1, m2)) = elmtclass e (App (m1, m2)) >>= minus
  | sortclass e (Case (m1, pml, m2)) = raise Fail ""
  | sortclass e (IfElse (m1, m2, m3)) =
      sortclass e m2 >>= (fn s2 =>
      sortclass e m3 >>= (fn s3 =>
        if s2 = s3 then return s2 else zero ()
      ))
  | sortclass e (Let (v, m1, m2, m3)) =
      envWithDel v m1 m2 e >>= (fn e' => sortclass e' m3)
  | sortclass e (Lambda (v, m1, m2)) =
      elmtclass e (Lambda (v, m1, m2)) >>= minus
  | sortclass e (DepProduct (v, m1, m2)) =
      sortclass e m1 >>= (fn s1 =>
      envWithTy v m1 e >>= (fn e' =>
      sortclass e' m2 >>= (fn s2 => rho s1 s2)))
  | sortclass e (DepSum (v, m1, m2)) =
      sortclass e m1 >>= (fn s1 =>
      envWithTy v m1 e >>= (fn e' =>
      sortclass e' m2 >>= (fn s2 => rho s1 s2)))
  | sortclass e (Tuple (m1, m2, m3)) = raise Fail ""
  | sortclass e (First m) = raise Fail ""
  | sortclass e (Second m) = raise Fail ""

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
      ++ (case m1 of
          Lambda (v, m3, m4) => subst v m2 m4
        )
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
      ++ (case m1 of
          Lambda (v, m3, m4) => subst v m2 m4
        )
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

  fun whsdcl e m =
    sdcl e m >>= (fn m' =>
    whreduce m' >>= (fn m'' =>
      return m''
    ))
  and sdcl e (Var v) =
      inEnv v e >>= (fn (e', m) =>
      let
        val m' = (case m of
          EnvTy (v', m') => m'
        | EnvDel (v', m1, m2) => m1)
      in
        whsdcl e' m' >>= (fn m'' =>
        isSort m'' >>= (fn _ =>
        return m'))
      end)
  | sdcl e (Lit (IntLit _)) = return (Lit (IntTyLit))
  | sdcl e (Lit (BoolLit _)) = return (Lit (BoolTyLit))
  | sdcl e (Lit (IntTyLit)) = return (Sort TypeVal)
  | sdcl e (Lit (BoolTyLit)) = return (Sort TypeVal)
  | sdcl e (Sort s) = hasAxiom s >>= (fn s' => return (Sort s'))
  | sdcl e (App (m1, m2)) =
      whsdcl e m1 >>= (fn m1' =>
      sdcl e m2 >>= (fn m2' =>
        (case m1' of
          DepProduct (v, m1'', m2'') => subst v m2 m2'')))
  | sdcl e (Case (m1, pml, m2)) = raise Fail ""
  | sdcl e (IfElse (m1, m2, m3)) =
      sdcl e m1 >>= (fn m1' =>
      whsdcl e m2 >>= (fn m2' =>
      whsdcl e m3 >>= (fn m3' =>
      bequiv m2' m3' >>= (fn _ =>
        (case m1' of
          Lit BoolTyLit => return m2')))))
  | sdcl e (Let (v, m1, m2, m3)) =
      whsdcl e m1 >>= (fn m1' =>
      isSort m1' >>= (fn _ =>
      whsdcl e m2 >>= (fn m2' =>
      bequiv m1 m2' >>= (fn _ =>
      envWithTy v m1 e >>= (fn e' =>
      whsdcl e' m3 >>= (fn m3' =>
      return (Let (v, m1, m2, m3'))))))))
  | sdcl e (Lambda (v, m1, m2)) =
      envWithTy v m1 e >>= (fn e' =>
      sdcl e' m2 >>= (fn m2' =>
      elmtclass e (Lambda (v, m1, m2)) >>= (fn _ =>
      return (DepProduct (v, m1, m2')))))
  | sdcl e (DepProduct (v, m1, m2)) =
      sortclass e m1 >>= (fn s1 =>
      envWithTy v m1 e >>= (fn e' =>
      whsdcl e' m2 >>= (fn m2' =>
      isSort m2' >>= (fn s2 =>
      rho s1 s2 >>= (fn s3 => return (Sort s3))))))
  | sdcl e (DepSum (v, m1, m2)) = raise Fail ""
  | sdcl e (Tuple (m1, m2, m3)) = raise Fail ""
  | sdcl e (First m) = raise Fail ""
  | sdcl e (Second m) = raise Fail ""

  fun checkVal e (v, m1, m2) = raise Fail ""
  fun checkData e (tname, tm, dcml) = raise Fail ""
  fun checkNewTy e (cname, cm, dname, dm) = raise Fail ""
  fun checkClass e (clname, cml) = raise Fail ""
  fun checkInstance e (clname, iname, cml) = raise Fail ""

end

