datatype TypeError =
  EmptyError
| Expected of Lang.ty * Lang.ty
| VarNotInEnv of Lang.var

type typestate = {
  errs : TypeError list
}

structure M = StateFunctor(type s = typestate)

structure TypeCheckMonad = OptionT (structure M = M)

structure TypeCheck : sig
  type typeenv = (Lang.var * Lang.ty) list

  val put_error : TypeError -> unit TypeCheckMonad.monad
  val failCheck : TypeError -> Lang.ty TypeCheckMonad.monad
  val check : typeenv -> Lang.term -> Lang.ty TypeCheckMonad.monad
end
=
struct
  open TypeCheckMonad

  type typeenv = (Lang.var * Lang.ty) list

  fun put_error error =
    lift M.get >>= (fn (s : typestate) =>
    lift (M.put ({ errs = error::(#errs s) }))
    )
  and failCheck error = 
    put_error error >>= (fn _ =>
      fail ()
    )

  fun check tyenv (Lang.IntLit i) = return (Lang.IntTy)
  | check tyenv (Lang.Var v) = 
      (case List.find (fn x => #1 x = v) tyenv of
        SOME (_, t) => return t
      | NONE => failCheck (VarNotInEnv v)
      )
  | check tyenv (Lang.Lambda (x, m, argt)) = 
      check ((x, argt)::tyenv) m >>= (fn t =>
        return (Lang.FuncTy (argt, t))
      )
  | check tyenv (Lang.First (m)) =
      check tyenv m >>= (fn t =>
        (case t of
          Lang.TupleTy (t1, t2) => return t1
        | _ => failCheck (EmptyError))
      )
  | check tyenv (Lang.Second (m)) =
      check tyenv m >>= (fn t =>
        (case t of
          Lang.TupleTy (t1, t2) => return t2
        | _ => failCheck (EmptyError))
      )
  | check tyenv (Lang.Tuple (m1, m2)) = 
      check tyenv m1 >>= (fn t1 =>
      check tyenv m2 >>= (fn t2 =>
        return (Lang.TupleTy (t1, t2))
      ))
  | check tyenv (Lang.Let (x, m1, m2, argt)) = 
      check tyenv m1 >>= (fn t1 =>
      check tyenv m2 >>= (fn t2 =>
        if t1 = argt then return t2
        else failCheck (EmptyError)
      ))
  | check tyenv (Lang.IfZero (m1, m2, m3)) = 
      check tyenv m1 >>= (fn t1 =>
      check tyenv m2 >>= (fn t2 =>
      check tyenv m3 >>= (fn t3 =>
        (case t1 of
          Lang.IntTy =>
            if t2 = t3 then return t2
            else failCheck (EmptyError)
        | _ => failCheck (EmptyError))
      )))
  | check tyenv (Lang.App (m1, m2)) = 
      check tyenv m1 >>= (fn t1 =>
      check tyenv m2 >>= (fn t2 =>
        (case t1 of
          Lang.FuncTy (t3, t4) => 
            if t3 = t2 then return t4
            else failCheck (EmptyError)
        | _ => failCheck (EmptyError))
      ))
  | check tyenv (Lang.PrimApp (opr, m)) = 
      check tyenv m >>= (fn t =>
        (case t of
          Lang.TupleTy (Lang.IntTy, Lang.IntTy) => return Lang.IntTy
        | _ => failCheck (EmptyError))
      )

end

