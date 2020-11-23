structure Term : sig
  type 'a monad = 'a InterpM.monad
  val isLambda : MTS.term -> (MTS.var * MTS.term * MTS.term) monad
  val isDepProduct : MTS.term -> (MTS.var * MTS.term * MTS.term) monad
  val isBoolTy : MTS.term -> unit monad
  val isStruct : MTS.modexpr -> ((MTS.var * MTS.var) * MTS.def) list monad
  val isFunctor : MTS.modexpr -> (MTS.var * MTS.modtype * MTS.modexpr) monad
  val isSig : MTS.modtype
    -> ((MTS.var * MTS.var) * MTS.specification) list monad
  val isFuncT : MTS.modtype -> (MTS.var * MTS.modtype * MTS.modtype) monad
end
=
struct
  type 'a monad = 'a InterpM.monad
  open InterpM
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

end

