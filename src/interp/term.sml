structure Term : sig
  type 'a monad = 'a MTSInterpM.monad
  val isLambda : MTS.term -> (MTS.var * MTS.term * MTS.term) monad
  val isDepProduct : MTS.term -> (MTS.var * MTS.term * MTS.term) monad
  val isBoolTy : MTS.term -> unit monad
  val isStruct : MTS.modexpr -> (MTS.var * MTS.def) list monad
  val isFunctor : MTS.modexpr -> (MTS.var * MTS.modtype * MTS.modexpr) monad
  val isSig : MTS.modtype -> (MTS.var * MTS.specification) list monad
  val isFuncT : MTS.modtype -> (MTS.var * MTS.modtype * MTS.modtype) monad
  val isInductive : MTS.term -> (MTS.var * MTS.term * MTS.term list) monad
  val arity : MTS.term -> MTS.sort monad
  val strictlyPositive : MTS.var -> MTS.term -> unit monad
  val constructorForm : MTS.var -> MTS.term -> unit monad
  val sigbodyContains : MTS.var -> (MTS.var * MTS.specification) list
    -> MTS.specification monad
  val structbodyContains : MTS.modexpr -> MTS.var
    -> (MTS.var * MTS.def) list -> MTS.def monad
  val structDef : MTS.path -> MTS.def monad
end = struct
  type 'a monad = 'a MTSInterpM.monad
  open MTSInterpM
  open Util
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
  fun isInductive (Inductive ((v, t), tl)) = return (v, t, tl)
    | isInductive _ = throw ()
  fun arity (Path p) = throw ()
    | arity (Lit _) = throw ()
    | arity (Sort s') = return s'
    | arity (App (t1, t2)) = throw ()
    | arity (Case (t, alts)) = throw ()
    | arity (IfElse (t1, t2, t3)) = throw ()
    | arity (Let (v, t1, t2, t3)) = throw ()
    | arity (Lambda (v, t1, t2)) = throw ()
    | arity (DepProduct (v, t1, t2)) = arity t2
    | arity (Inductive _) = throw ()
    | arity (Constr _) = throw ()
  fun strictlyPositive c (Path (PVar v)) = 
    if eqv c v then return () else throw ()
    | strictlyPositive c (Path (PPath (p, v))) = throw ()
    | strictlyPositive c (Lit _) = throw ()
    | strictlyPositive c (Sort _) = throw ()
    | strictlyPositive c (App (t1, t2)) = 
      strictlyPositive c t1 >>
      (if Set.member c (fvTerm t2) then throw () else return ())
    | strictlyPositive c (Case (t, alts)) = throw ()
    | strictlyPositive c (IfElse (t1, t2, t3)) = throw ()
    | strictlyPositive c (Let (v, t1, t2, t3)) = throw ()
    | strictlyPositive c (Lambda (v, t1, t2)) = throw ()
    | strictlyPositive c (DepProduct (v, t1, t2)) =
      strictlyPositive c t2 >>
      (if Set.member c (fvTerm t1) then throw () else return ())
    | strictlyPositive c (Inductive _) = throw ()
    | strictlyPositive c (Constr _) = throw ()
  fun constructorForm c (Path (PVar v)) = 
    if eqv c v then return () else throw ()
    | constructorForm c (Path (PPath (p, v))) = throw ()
    | constructorForm c (Lit _) = throw ()
    | constructorForm c (Sort _) = throw ()
    | constructorForm c (App (t1, t2)) = 
      constructorForm c t1 >>
      (if Set.member c (fvTerm t2) then throw () else return ())
    | constructorForm c (Case (t, alts)) = throw ()
    | constructorForm c (IfElse (t1, t2, t3)) = throw ()
    | constructorForm c (Let (v, t1, t2, t3)) = throw ()
    | constructorForm c (Lambda (v, t1, t2)) = throw ()
    | constructorForm c (DepProduct (AnonVar, t1, t2)) =
      strictlyPositive c t1 >> constructorForm c t2
    | constructorForm c (DepProduct (v, t1, t2)) =
      (if Set.member v (fvTerm t2) then
        constructorForm c t2 >>
        (if Set.member c (fvTerm t1) then throw ()
        else return ())
      else constructorForm c t2 >> strictlyPositive c t1)
    | constructorForm c (Inductive _) = throw ()
    | constructorForm c (Constr _) = throw ()
  fun sigbodyContains v sl =
    (case List.find (fn (v', _) => eqv v v') sl of
      SOME (_, s) => return s
    | _ => throw ())
  fun structbodyContains p v dl =
    let fun f _ ([]) = throw ()
      | f dl'' ((v', d)::dl') =
        if eqv v v' then return ((v', d), List.rev dl'')
        else f ((v', d)::dl'') dl'
    in f [] dl >>= (fn ((_, d), dl') =>
      return (foldl (fn ((v', _), d') =>
        PSub.substDef v' (PPath (p, v')) d') d dl')) end
  fun structDef (PPath (p, v)) =
    isStruct p >>= (fn dl => structbodyContains p v dl)
    | structDef (PVar v) = zero ()
end
