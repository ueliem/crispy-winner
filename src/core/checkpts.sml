datatype TypeError =
  Expected of PTS.term * PTS.term
| Mismatch of PTS.term * PTS.term
| TermError of PTS.term
| NoAxiom of PTS.sort
| NoRule of PTS.term * PTS.sort * PTS.sort
| NoSort of PTS.term * PTS.term
| NoSortForTerm of PTS.term

type typestate = {
  deltas : PTS.defs,
  errs : TypeError list
}

structure TypeCheckMonad = StateFunctor(type s = typestate)

structure TypeCheck : sig
  val get_defs : unit -> PTS.defs TypeCheckMonad.monad
  val put_error : TypeError -> unit TypeCheckMonad.monad
  val fail : TypeError -> PTS.term TypeCheckMonad.monad
  val whcheck_sfsd : PTS.spec -> PTS.env -> PTS.term -> PTS.term TypeCheckMonad.monad
  val whcheck_nat : PTS.spec -> PTS.env -> PTS.term -> PTS.term TypeCheckMonad.monad
  val check_sfsd : PTS.spec -> PTS.env -> PTS.term -> PTS.term TypeCheckMonad.monad
  val check_nat : PTS.spec -> PTS.env -> PTS.term -> PTS.term TypeCheckMonad.monad
end
=
struct
  open TypeCheckMonad

  fun get_defs () =
    get >>= (fn s =>
      return (#deltas s)
    )
  and put_error error =
    get >>= (fn s =>
    put ({ deltas = #deltas s, errs = error::(#errs s) })
    )
  and fail error = 
    put_error error >>= (fn _ =>
      return (PTS.Unknown)
    )

  fun whcheck_sfsd sp env t =
    check_sfsd sp env t >>= (fn x =>
    get_defs () >>= (fn d =>
      return (PTS.whreduce d x)
    ))
  and whcheck_nat sp env t =
    check_nat sp env t >>= (fn x =>
    get_defs () >>= (fn d =>
      return (PTS.whreduce d x)
    ))
  and check_sfsd sp env t =
    case t of 
      PTS.Sort s =>
      (case List.find (fn a => #1 a = s) (#2 sp) of
        SOME s' => return (PTS.Sort (#2 s'))
      | NONE => fail (NoAxiom s))
    | PTS.Variable n =>
      let val a = List.nth (env, n - 1)
      in
        whcheck_sfsd sp env a >>= (fn b =>
          case b of
            PTS.Sort s => return a
          | _ => fail (TermError t)
        )
      end
    | PTS.Literal l =>
      (case l of
        PTS.IntLit i => return (PTS.Sort PTS.IntSort)
      | PTS.BoolLit b => return (PTS.Sort PTS.BoolSort)
      )
    | PTS.Abs (t1, t2) =>
      check_sfsd sp env t1 >>= (fn t1' =>
      check_sfsd sp (t1::env) t2 >>= (fn t2' =>
        case t1' of
          PTS.Sort s =>
            (case List.find (fn a => #1 a = s) (#2 sp) of
              SOME _ => return (PTS.DepProd (t1, t2'))
            | NONE => fail (TermError t))
        | _ => fail (TermError t)
      ))
    | PTS.App (t1, t2) =>
      whcheck_sfsd sp env t1 >>= (fn t1' =>
      check_sfsd sp env t2 >>= (fn t2' =>
      get_defs () >>= (fn d =>
        case t1' of
          PTS.DepProd (t3, t4) => 
            let 
              val t2'' = PTS.nfreduce d t2'
              val t3' = PTS.nfreduce d t3
            in
              if t2'' = t3' then
                return (PTS.subst 1 t2 t4)
              else fail (TermError t)
            end
        | _ => fail (TermError t)
      )))
    | PTS.DepProd (t1, t2) =>
      whcheck_sfsd sp env t1 >>= (fn t1' =>
      whcheck_sfsd sp (t1::env) t2 >>= (fn t2' =>
        case (t1', t2') of
          (PTS.Sort s1, PTS.Sort s2) =>
            (case PTS.rho sp (SOME s1, SOME s2) of
              SOME s3 => return (PTS.Sort s3)
            | NONE => fail (TermError t)
            )
        | _ => fail (TermError t)
      ))
    | PTS.LetTerm (t1, t2, t3) =>
      check_sfsd sp env t2 >>= (fn t2' =>
      check_sfsd sp env t3 >>= (fn t3' =>
      get_defs () >>= (fn d =>
        let 
          val t1' = PTS.nfreduce d t1
          val t2'' = PTS.nfreduce d t2'
        in
          if t1' = t2'' then
            return (PTS.LetTerm (t1', t2, t3'))
          else fail (TermError t)
        end
      )))
    | PTS.DepSum (t1, t2) =>
      whcheck_sfsd sp env t1 >>= (fn t1' =>
      whcheck_sfsd sp (t1::env) t2 >>= (fn t2' =>
        case (t1', t2') of
          (PTS.Sort s1, PTS.Sort s2) =>
            (case PTS.rho sp (SOME s1, SOME s2) of
              SOME s3 => return (PTS.Sort s3)
            | NONE => fail (TermError t)
            )
        | _ => fail (TermError t)
      ))
    | PTS.DepPair (t1, t2, t3) =>
        check_sfsd sp env t1 >>= (fn t1' =>
        check_sfsd sp (t1::env) t2 >>= (fn t2' =>
        get_defs () >>= (fn d =>
          (case t3 of
            PTS.DepSum (t4, t5) =>
              let 
                val t1'' = PTS.nfreduce d t1'
                val t4' = PTS.nfreduce d t4
                val t2'' = PTS.nfreduce d (PTS.subst 1 t1 t2')
                val t5' = PTS.nfreduce d (PTS.subst 1 t1 t5)
              in
                if t4' = t1'' then
                  if t5' = t2'' then
                    return t3
                  else fail (TermError t)
                else fail (TermError t)
              end
          | _ => fail (TermError t))
        )))
    | PTS.Fst t1 =>
        check_sfsd sp env t1 >>= (fn x =>
          (case x of
            PTS.DepSum (t2, t3) => return t2
          | _ => fail (TermError t))
        )
    | PTS.Snd t1 =>
        check_sfsd sp env t1 >>= (fn x =>
          (case x of
            PTS.DepSum (t2, t3) => return (PTS.subst 1 (PTS.Fst t1) t3)
          | _ => fail (TermError t))
        )
    | PTS.Unknown => return PTS.Unknown
  and check_nat sp env t =
    case t of 
      PTS.Sort s =>
      (case List.find (fn a => #1 a = s) (#2 sp) of
        SOME s' => return (PTS.Sort (#2 s'))
      | NONE => fail (NoAxiom s))
    | PTS.Variable n =>
      let val a = List.nth (env, n - 1)
      in
        whcheck_nat sp env a >>= (fn b =>
          case b of
            PTS.Sort s => return a
          | _ => fail (TermError t)
        )
      end
    | PTS.Literal l =>
      (case l of
        PTS.IntLit i => return (PTS.Sort PTS.IntSort)
      | PTS.BoolLit b => return (PTS.Sort PTS.BoolSort)
      )
    | PTS.Abs (t1, t2) =>
        check_nat sp (t1::env) t2 >>= (fn t2' =>
        check_sfsd sp env (PTS.DepProd (t1, t2')) >>= (fn t1' =>
          (case t1' of
            PTS.Sort s => return (PTS.DepProd (t1, t2'))
          | _ => fail (TermError t))
        ))
    | PTS.App (t1, t2) =>
      whcheck_nat sp env t1 >>= (fn t1' =>
      check_sfsd sp env t2 >>= (fn t2' =>
      get_defs () >>= (fn d =>
        case t1' of
          PTS.DepProd (t3, t4) => 
            let 
              val t2'' = PTS.nfreduce d t2'
              val t3' = PTS.nfreduce d t3
            in
              if t2'' = t3' then
                return (PTS.subst 1 t2 t4)
              else fail (TermError t)
            end
        | _ => fail (TermError t)
      )))
    | PTS.DepProd (t1, t2) =>
      whcheck_nat sp env t1 >>= (fn t1' =>
      whcheck_nat sp (t1::env) t2 >>= (fn t2' =>
        case (t1', t2') of
          (PTS.Sort s1, PTS.Sort s2) =>
            (case PTS.rho sp (SOME s1, SOME s2) of
              SOME s3 => return (PTS.Sort s3)
            | NONE => fail (TermError t)
            )
        | _ => fail (TermError t)
      ))
    | PTS.LetTerm (t1, t2, t3) =>
      check_nat sp env t2 >>= (fn t2' =>
      check_nat sp env t3 >>= (fn t3' =>
      get_defs () >>= (fn d =>
        let 
          val t1' = PTS.nfreduce d t1
          val t2'' = PTS.nfreduce d t2'
        in
          if t1' = t2'' then
            return (PTS.LetTerm (t1', t2, t3'))
          else fail (TermError t)
        end
      )))
    | PTS.DepSum (t1, t2) =>
      whcheck_nat sp env t1 >>= (fn t1' =>
      whcheck_nat sp (t1::env) t2 >>= (fn t2' =>
        case (t1', t2') of
          (PTS.Sort s1, PTS.Sort s2) =>
            (case PTS.rho sp (SOME s1, SOME s2) of
              SOME s3 => return (PTS.Sort s3)
            | NONE => fail (TermError t)
            )
        | _ => fail (TermError t)
      ))
    | PTS.DepPair (t1, t2, t3) =>
        check_nat sp env t1 >>= (fn t1' =>
        check_nat sp (t1::env) t2 >>= (fn t2' =>
        get_defs () >>= (fn d =>
          (case t3 of
            PTS.DepSum (t4, t5) =>
              let 
                val t1'' = PTS.nfreduce d t1'
                val t4' = PTS.nfreduce d t4
                val t2'' = PTS.nfreduce d (PTS.subst 1 t1 t2')
                val t5' = PTS.nfreduce d (PTS.subst 1 t1 t5)
              in
                if t4' = t1'' then
                  if t5' = t2'' then
                    return t3
                  else fail (TermError t)
                else fail (TermError t)
              end
          | _ => fail (TermError t))
        )))
    | PTS.Fst t1 =>
        check_nat sp env t1 >>= (fn x =>
          (case x of
            PTS.DepSum (t2, t3) => return t2
          | _ => fail (TermError t))
        )
    | PTS.Snd t1 =>
        check_nat sp env t1 >>= (fn x =>
          (case x of
            PTS.DepSum (t2, t3) => return (PTS.subst 1 (PTS.Fst t1) t3)
          | _ => fail (TermError t))
        )
    | PTS.Unknown => return PTS.Unknown

end

