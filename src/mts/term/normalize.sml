structure Normalize : sig
  type 'a monad = 'a InterpM.monad
  val whstep : MTS.term -> MTS.term monad
  val whreduce : MTS.term -> MTS.term monad
  val nfstep : MTS.term -> MTS.term monad
  val nfreduce : MTS.term -> MTS.term monad
  val mexprstep : MTS.modexpr -> MTS.modexpr monad
  val mexprreduce : MTS.modexpr -> MTS.modexpr monad
  val bequiv : MTS.term -> MTS.term -> unit monad
  val mequiv : MTS.modexpr -> MTS.modexpr -> unit monad

end
=
struct
  type 'a monad = 'a InterpM.monad
  open MTS
  open InterpM

  fun nfstep (Path _) = zero ()
  | nfstep (Lit _) = zero ()
  | nfstep (Sort _) = zero ()
  | nfstep (App (m1, m2)) =
      (nfstep m1 >>= (fn m1' => return (App (m1', m2))))
      ++ (nfstep m2 >>= (fn m2' => return (App (m1, m2'))))
      ++ (Term.isLambda m1 >>= (fn (v, m3, m4) => return (TSub.substTerm v m2 m4)))
  | nfstep (Case (m1, pml)) = raise Fail ""
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

  fun whstep (Path _) = zero ()
  | whstep (Lit _) = zero ()
  | whstep (Sort _) = zero ()
  | whstep (App (m1, m2)) =
      (whstep m1 >>= (fn m1' => return (App (m1', m2))))
      ++ (Term.isLambda m1 >>= (fn (v, m3, m4) => return (TSub.substTerm v m2 m4)))
  | whstep (Case (m, pml)) =
      (whstep m >>= (fn m' => return (Case (m', pml))))
      ++ (return (raise Fail ""))
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

  fun mexprstep (ModStruct dl) = throw ()
  | mexprstep (ModFunctor (v, m1, m2)) = throw ()
  | mexprstep (ModApp (m1, m2)) =
      (mexprstep m1 >>= (fn m1' => return (ModApp (m1', m2))))
      ++ (Term.isFunctor m1 >>= (fn (v, m3, m4) => return (MSub.substModexpr v m2 m4)))
  | mexprstep (ModPath (PPath (p, v))) =
      (mexprstep p >>= (fn p' => return (ModPath (PPath (p', v)))))
      ++ (Term.isStruct p >>= (fn dl =>
        let
          fun f _ ([]) = throw ()
          | f dl'' (((v', v''), d)::dl') =
              if eqv v v' then return (((v', v''), d), List.rev dl'')
              else f (((v', v''), d)::dl'') dl'
        in
          f [] dl >>= (fn (((v', v''), d), dl') =>
          getDefModexpr d >>= (fn m =>
          return (foldl (fn (((_, v'''), _), m') =>
            PSub.substModexpr v''' (PPath (p, v''')) m') m dl')))
        end))
      ++ (PseudoType.pseudoTModexpr p >>= (fn s =>
        getSpecModtype s >>= (fn s' =>
        Term.isSig s' >>= (fn s'' =>
        (case List.find (fn ((v', _), _) => eqv v v') s'' of
          SOME ((_, _), SpecManifestMod (_, m)) => return m
        | _ => throw ())))))
  | mexprstep (ModPath (PVar v)) = throw ()

  fun mexprreduce m =
    (mexprstep m >>= (fn m' => mexprreduce m')) ++ return m

  fun bequiv m1 m2 =
    nfreduce m1 >>= (fn m1' =>
    nfreduce m2 >>= (fn m2' =>
      if Equiv.eq m1' m2' then return ()
      else throw ()))

  fun mequiv m1 m2 =
    mexprreduce m1 >>= (fn m1' =>
    mexprreduce m2 >>= (fn m2' =>
      if Equiv.mexpreq m1' m2' then return ()
      else throw ()))

end

