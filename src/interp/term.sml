structure Term : sig
  type 'a monad = 'a MTSInterpM.monad
  val isLambda : MTS.term -> (MTS.var * MTS.term * MTS.term) monad
  val isDepProduct : MTS.term -> (MTS.var * MTS.term * MTS.term) monad
  val isBoolTy : MTS.term -> unit monad
  val isStruct : MTS.modexpr -> ((MTS.var * MTS.var) * MTS.def) list monad
  val isFunctor : MTS.modexpr -> (MTS.var * MTS.modtype * MTS.modexpr) monad
  val isSig : MTS.modtype
    -> ((MTS.var * MTS.var) * MTS.specification) list monad
  val isFuncT : MTS.modtype -> (MTS.var * MTS.modtype * MTS.modtype) monad

  val leftmost : MTS.term -> MTS.var monad
  (* val collectArgs : MTS.term -> MTS.term list monad
  val wfTCType : MTS.term -> unit monad
  val wfDCType : MTS.term -> unit monad *)
end = struct
  type 'a monad = 'a MTSInterpM.monad
  open MTSInterpM
  open MTS
  fun isLambda (Lambda (v, m1, m2)) = return (v, m1, m2)
    | isLambda _ = throw ()
  fun isDepProduct (DepProduct (v, m1, m2)) = return (v, m1, m2)
    | isDepProduct _ = throw ()
  fun isBoolTy (Lit BoolTyLit) = return ()
    | isBoolTy _ = throw ()
  fun isStruct (ModStruct s) = return s
    | isStruct _ = throw ()
  fun isFunctor (ModFunctor (v, m1, m2)) = return (v, m1, m2)
    | isFunctor _ = throw ()
  fun isSig (ModTypeSig vsl) = return vsl
    | isSig _ = throw ()
  fun isFuncT (ModTypeFunctor (v, m1, m2)) = return (v, m1, m2)
    | isFuncT _ = throw ()
  fun leftmost (App (m1, m2)) = leftmost m1
    | leftmost (Path (PVar v)) = return v
    | leftmost _ = throw ()
  fun getArgTypes ([]) _ = return []
    | getArgTypes (x::xs) (DepProduct (v, m1, m2)) =
      getArgTypes xs m2 >>= (fn m2' => return (m1::m2'))
    | getArgTypes (x::xs) _ = throw ()
  (* fun collectArgs (DepProduct (v, m1, m2)) =
    collectArgs m2 >>= (fn args =>
    return (m1::args))
  | collectArgs (
  fun wfTCType (DepProduct (v, m1, m2)) =
  | wfTCType (Sort s) = 
  *)
end
