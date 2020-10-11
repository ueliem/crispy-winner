structure MTSCheck : sig
  include MONAD
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
  open InterpM
  open MTS

  fun isSort (Sort s) =
    getSorts () >>= (fn srts =>
      if List.exists (fn x => x = s) srts
      then return s else zero ())
  | isSort _ = zero ()

  fun isBottomSort srt =
    getSorts () >>= (fn srts =>
    getAxioms () >>= (fn axs =>
      if List.exists (fn (s1, s2) => s2 = srt) axs
      then zero () else return ()))

  fun isTopSort srt =
    getSorts () >>= (fn srts =>
    getAxioms () >>= (fn axs =>
      if List.exists (fn (s1, s2) => s1 = srt) axs
      then zero () else return ()))

  fun hasAxiom s1 =
    getAxioms () >>= (fn axs =>
      (case List.find (fn (s1', s2) => s1 = s1') axs of
        SOME (s1, s2) => return s2
      | NONE => zero ()))

  fun hasRule s1 s2 =
    getRules () >>= (fn rls =>
      (case List.find (fn (s1', s2', s3) => s1 = s1' andalso s2 = s2') rls of
        SOME (s1, s2, s3) => return s3
      | NONE => zero ()))

  fun startsRule s1 =
    getRules () >>= (fn rls =>
      (case List.find (fn (s1', s2', s3) => s1 = s1') rls of
        SOME (s1, s2, s3) => return ()
      | NONE => zero ()))

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

