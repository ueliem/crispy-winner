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
  val checkBoxValue : typeenv -> regionenv -> Lang.boxvalue -> (Lang.boxty * Lang.effect) TypeCheckMonad.monad
  val checkAbs : typeenv -> regionenv -> Lang.abs -> (Lang.boxty * Lang.effect) TypeCheckMonad.monad
  val runCheck : Lang.term -> (Lang.ty * Lang.effect) option * typestate
end
=
struct
  open TypeCheckMonad

  type typeenv = (Lang.var * Lang.ty) list
  type regionenv = Lang.regionvar list

  fun fail () = M.return NONE

  fun put_error error =
    lift M.get >>= (fn (s : typestate) =>
    lift (M.put ({ errs = error::(#errs s) }))
    )
  and failCheck error = 
    put_error error >>= (fn _ =>
      fail ()
    )

  fun check tyenv regenv (Lang.Value v) = checkValue tyenv regenv v
  | check tyenv regenv (Lang.BoxedValue v) = 
      checkBoxValue tyenv regenv v >>= (fn (t, phi) =>
        return (Lang.BoxedTy t, phi)
      )
  | check tyenv regenv (Lang.Var v) = 
      (case List.find (fn x => #1 x = v) tyenv of
        SOME (_, t) => return (t, [])
      | NONE => failCheck (VarNotInEnv v)
      )
  | check tyenv regenv (Lang.Select (i, m)) =
      check tyenv regenv m >>= (fn (t, phi) =>
        (case t of
          Lang.BoxedTy (Lang.BoxTupleTy (t1, r)) => return (List.nth (t1, i), Set.insert r phi)
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
      check tyenv (r::regenv) m >>= (fn (t, phi) =>
        return (t, Set.remove r phi)
      )
  | check tyenv regenv (Lang.RegionElim (f, r1, r2)) = 
      (case List.find (fn x => #1 x = f) tyenv of
        SOME (_, t) => 
          (case t of
            Lang.BoxedTy (Lang.BoxRegFuncTy (r4, t', phi1, r3)) => 
              if List.exists (fn x => x = r1) regenv then
                return (Lang.substRegVarTy (r4, r1) t', 
                  Set.insert r1 (Set.insert r2 (Set.insert r3 (Set.remove r4 phi1)))
                )
              else failCheck (EmptyError)
          | _ => failCheck (EmptyError)
          )
      | NONE => failCheck (VarNotInEnv f)
      )
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
      let
        fun f ([]) = return ([], [])
        | f (x::xs) = 
            check tyenv regenv x >>= (fn (t, phi) =>
            f xs >>= (fn (tl, phi1) =>
              return (t::tl, Set.union phi phi1)
            ))
      in
        check tyenv regenv m1 >>= (fn (t1, phi1) =>
        f m2 >>= (fn (t2, phi2) =>
          (case t1 of
            Lang.BoxedTy (Lang.BoxFuncTy (t3, t4, phi3, r)) => 
              if t3 = t2 then 
                return (t4, Set.insert r (Set.union phi1 (Set.union phi2 phi3)))
              else failCheck (EmptyError)
          | _ => failCheck (EmptyError))
        ))
      end
  | check tyenv regenv (Lang.PrimApp (opr, m1, m2)) = 
      check tyenv regenv m1 >>= (fn (t1, phi1) =>
      check tyenv regenv m2 >>= (fn (t2, phi2) =>
        (case (t1, t2) of
          (Lang.IntTy, Lang.IntTy) => 
            (case opr of
              "+" => return (Lang.IntTy, Set.union phi1 phi2)
            | "-" => return (Lang.IntTy, Set.union phi1 phi2)
            | "*" => return (Lang.IntTy, Set.union phi1 phi2)
            | "<" => return (Lang.BoolTy, Set.union phi1 phi2)
            | "=" => return (Lang.BoolTy, Set.union phi1 phi2)
            | _ => raise Fail "undefined operator"
            )
        | _ => failCheck (EmptyError))
      ))

  and checkValue tyenv regenv (Lang.IntLit i) = return (Lang.IntTy, [])
  | checkValue tyenv regenv (Lang.BoolLit b) = return (Lang.BoolTy, [])
  | checkValue tyenv regenv (Lang.UnitLit) = return (Lang.UnitTy, [])
  | checkValue tyenv regenv (Lang.BarePointer (r, p)) = 
      raise Fail "not known at compile time"

  and checkBoxValue tyenv regenv (Lang.BoxIntLit (i, rho)) = 
      return (Lang.BoxIntTy rho, [rho])
  | checkBoxValue tyenv regenv (Lang.BoxBoolLit (b, rho)) = 
      return (Lang.BoxBoolTy rho, [rho])
  | checkBoxValue tyenv regenv (Lang.BoxUnitLit rho) = 
      return (Lang.BoxUnitTy rho, [rho])
  | checkBoxValue tyenv regenv (Lang.BoxAbs a) = 
      checkAbs tyenv regenv a
  | checkBoxValue tyenv regenv (Lang.BoxTuple (m, rho)) = 
      let
        fun f ([]) = return ([], [])
        | f (x::xs) = 
            check tyenv regenv x >>= (fn (t, phi) =>
            f xs >>= (fn (tl, phi1) =>
              return (t::tl, Set.union phi phi1)
            ))
      in
        f m >>= (fn (tl, phi) =>
          return (Lang.BoxTupleTy (tl, rho), Set.insert rho phi)
        )
      end
      (* map (fn x => 
        check tyenv regenv x >>= (fn (t, phi1) =>
          return (t, phi1)
        )) m *)
      (* check tyenv regenv m1 >>= (fn (t1, phi1) =>
      check tyenv regenv m2 >>= (fn (t2, phi2) =>
        return (Lang.BoxTupleTy (t1, t2, rho), Set.insert rho (Set.union phi1 phi2))
      )) *)
  | checkBoxValue tyenv regenv (Lang.BoxBarePointer (r, p, rho)) = 
      raise Fail "not known at compile time"

  and checkAbs tyenv regenv (Lang.Lambda (x, m, argt, rho)) = 
      check (ListPair.zipEq (x, argt) @ tyenv) regenv m >>= (fn (t, phi) =>
        if List.exists (fn x => x = rho) regenv then
          return (Lang.BoxFuncTy (argt, t, phi, rho), [rho])
        else failCheck (EmptyError)
      )
  | checkAbs tyenv regenv (Lang.RegionLambda (r, m, rho)) = 
      checkAbs tyenv (r::regenv) m >>= (fn (t, phi) =>
      if List.exists (fn x => x = rho) regenv then
        return (Lang.BoxRegFuncTy (r, Lang.BoxedTy t, phi, rho), [rho])
      else failCheck (EmptyError)
      )

  fun runCheck prog = 
    ((check [] [] prog) { errs = [] })

end
