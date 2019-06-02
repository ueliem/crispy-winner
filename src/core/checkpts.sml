datatype TypeError =
  Expected of PTS.term * PTS.term
| Unbound of PTS.vname
| CannotApply of PTS.term * PTS.term
| CannotUnify of PTS.term * PTS.term
| NoAxiom of PTS.sort
| TermError of PTS.term
| NoSort of PTS.term * PTS.term
| NoSortForTerm of PTS.term
| NoRule of PTS.term * PTS.sort * PTS.sort

type gamma = (PTS.vname, PTS.term) AssocList.asl

type typestate = {
  pairs : gamma,
  errs : TypeError list
}

structure TypeCheckMonad = StateFunctor(type s = typestate)

structure TypeCheck : sig
  val fail : TypeError -> PTS.term TypeCheckMonad.monad
  val get_term_ty : PTS.vname -> PTS.term TypeCheckMonad.monad
  val set_term_ty : PTS.vname -> PTS.term -> unit TypeCheckMonad.monad
  val whcheck : PTS.spec -> gamma -> PTS.term -> PTS.term TypeCheckMonad.monad
  val check : PTS.spec -> gamma -> PTS.term -> PTS.term TypeCheckMonad.monad
end
=
struct
  open TypeCheckMonad

  fun fail error = 
    get >>= (fn s =>
    put ({ pairs = #pairs s, errs = error::(#errs s) }) >>= (fn _ =>
      return PTS.Unknown
    ))

  fun get_term_ty v =
    get >>= (fn s =>
      case AssocList.get v (#pairs s) of
        SOME t => return t
      | NONE => fail (Unbound v)
    )

  fun set_term_ty v t =
    get >>= (fn s =>
    put ({ pairs = AssocList.insert (v, t) (#pairs s), errs = #errs s}) >>= (fn _ =>
      return ()
    ))

  fun whcheck sp env t =
    check sp env t >>= (fn x =>
      return (PTS.whreduce x)
    )
  and check sp env (PTS.Variable (v, t)) = return t
  | check sp env (PTS.Sort s) =
      (case List.find (fn a => #1 a = s) (#2 sp) of
        SOME s' => return (PTS.Sort (#2 s'))
      | NONE => fail (NoAxiom s))
  | check sp env (PTS.Literal l) =
      (case l of
        PTS.IntType => return (PTS.Sort PTS.ProperTypes)
      | PTS.IntLit i => return (PTS.Sort PTS.IntSort)
      )
  | check sp env (PTS.Abs (v, t1, t2)) =
      check sp env t1 >>= (fn x =>
        case PTS.rho sp (PTS.sort sp env (SOME t1), PTS.elmt sp env (SOME t2)) of
          SOME _ => return (PTS.DepProd (v, t1, x))
        | NONE => fail (TermError (PTS.Abs (v, t1, t2)))
      )
  | check sp env (PTS.App (t1, t2)) = 
      whcheck sp env t1 >>= (fn t1' =>
      check sp env t2 >>= (fn t2' =>
        (case t1' of
          PTS.DepProd (v, t3, t4) => 
            let 
              val t2'' = PTS.nfreduce t2'
              val t3' = PTS.nfreduce t3
            in
              if t2'' = t3' then
                return (PTS.weaksubst (v, t2) t4)
              else fail (CannotUnify (t2'', t3'))
            end
        | t => fail (TermError t)
        )
      ))
  | check sp env (PTS.DepProd (v, t1, t2)) =
      check sp env t2 >>= (fn x =>
        let
          val t2' = PTS.whreduce x
          val t1sort = PTS.sort sp env (SOME t1)
        in
          (case t1sort of
            SOME s1 => 
              (case t2' of
                PTS.Sort s2 => 
                  (case PTS.rho sp (SOME s1, SOME s2) of
                    SOME s3 => return (PTS.Sort s3)
                  | NONE => fail (NoRule (PTS.DepProd (v, t1, t2), s1, s2)))
              | _ => fail (NoSort (PTS.DepProd (v, t1, t2), t2')))
          | NONE => fail (NoSortForTerm t1))
        end
      )
  | check sp env (PTS.Unknown) = return PTS.Unknown
end

