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
  type regionenv = Lang.regionvar list

  val put_error : TypeError -> unit TypeCheckMonad.monad
  val failCheck : TypeError -> (Lang.ty * Lang.effect) TypeCheckMonad.monad
  val check : typeenv -> regionenv -> Lang.term -> (Lang.ty * Lang.effect) TypeCheckMonad.monad
  val checkValue : typeenv -> regionenv -> Lang.value -> (Lang.ty * Lang.effect) TypeCheckMonad.monad
end
=
struct
  open TypeCheckMonad

  type typeenv = (Lang.var * Lang.ty) list
  type regionenv = Lang.regionvar list

  fun put_error error =
    lift M.get >>= (fn (s : typestate) =>
    lift (M.put ({ errs = error::(#errs s) }))
    )
  and failCheck error = 
    put_error error >>= (fn _ =>
      fail ()
    )

  fun check tyenv regenv (Lang.Value v) = checkValue tyenv regenv v
  | check tyenv regenv (Lang.BoxedValue (v, r)) = 
      checkValue tyenv regenv v >>= (fn (t, phi) =>
        return (Lang.BoxedTy (t, r), Set.union phi [r])
      )
  | check tyenv regenv (Lang.BarePointer (r, p)) = 
      raise Fail "unknown at compile time"
  | check tyenv regenv (Lang.Var v) = 
      (case List.find (fn x => #1 x = v) tyenv of
        SOME (_, t) => return (t, [])
      | NONE => failCheck (VarNotInEnv v)
      )
  | check tyenv regenv (Lang.First (m)) =
      check tyenv regenv m >>= (fn (t, phi) =>
        (case t of
          Lang.TupleTy (t1, t2) => return (t1, phi)
        | _ => failCheck (EmptyError))
      )
  | check tyenv regenv (Lang.Second (m)) =
      check tyenv regenv m >>= (fn (t, phi) =>
        (case t of
          Lang.TupleTy (t1, t2) => return (t2, phi)
        | _ => failCheck (EmptyError))
      )
  | check tyenv regenv (Lang.Unbox m) = 
      check tyenv regenv m >>= (fn (t, phi) =>
        return (t, phi)
      )
  | check tyenv regenv (Lang.Let (x, m1, m2, argt)) = 
      check tyenv regenv m1 >>= (fn (t1, phi1) =>
      check tyenv regenv m2 >>= (fn (t2, phi2) =>
        if t1 = argt then return (t2, Set.union phi1 phi2)
        else failCheck (EmptyError)
      ))
  | check tyenv regenv (Lang.LetRegion (r, m)) = 
      check tyenv (Set.insert r regenv) m
  | check tyenv regenv (Lang.IfElse (m1, m2, m3)) = 
      check tyenv regenv m1 >>= (fn (t1, phi1) =>
      check tyenv regenv m2 >>= (fn (t2, phi2) =>
      check tyenv regenv m3 >>= (fn (t3, phi3) =>
        (case t1 of
          Lang.BoolTy =>
            if t2 = t3 then return (t2, Set.union (Set.union phi1 phi2) phi3)
            else failCheck (EmptyError)
        | _ => failCheck (EmptyError))
      )))
  | check tyenv regenv (Lang.App (m1, m2)) = 
      check tyenv regenv m1 >>= (fn (t1, phi1) =>
      check tyenv regenv m2 >>= (fn (t2, phi2) =>
        (case t1 of
          Lang.FuncTy (t3, t4) => 
            if t3 = t2 then return (t4, Set.union phi1 phi2)
            else failCheck (EmptyError)
        | _ => failCheck (EmptyError))
      ))
  | check tyenv regenv (Lang.PrimApp (opr, m)) = 
      check tyenv regenv m >>= (fn (t, phi) =>
        (case t of
          Lang.TupleTy (Lang.IntTy, Lang.IntTy) => 
            (case opr of
              "+" => return (Lang.IntTy, phi)
            | "-" => return (Lang.IntTy, phi)
            | "*" => return (Lang.IntTy, phi)
            | "<" => return (Lang.BoolTy, phi)
            | "=" => return (Lang.BoolTy, phi)
            | _ => raise Fail "undefined operator"
            )
        | _ => failCheck (EmptyError))
      )

  and checkValue tyenv regenv (Lang.IntLit i) = return (Lang.IntTy, [])
  | checkValue tyenv regenv (Lang.BoolLit b) = return (Lang.BoolTy, [])
  | checkValue tyenv regenv (Lang.UnitLit) = return (Lang.UnitTy, [])
  | checkValue tyenv regenv (Lang.Lambda (x, m, argt)) = 
      check ((x, argt)::tyenv) regenv m >>= (fn (t, phi) =>
        return (Lang.FuncTy (argt, t), phi)
      )
  | checkValue tyenv regenv (Lang.Tuple (m1, m2)) = 
      check tyenv regenv m1 >>= (fn (t1, phi1) =>
      check tyenv regenv m2 >>= (fn (t2, phi2) =>
        return (Lang.TupleTy (t1, t2), Set.union phi1 phi2)
      ))

end

