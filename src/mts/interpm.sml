structure InterpM : sig
  include MONADZEROPLUS
  type enventry = MTS.var * MTS.specification
  type env = enventry list
  type s = MTS.sorts * MTS.ax * MTS.rules

  val getstate : s monad
  val putstate : s -> unit monad
  val ask : env monad
  val loc : (env -> env) -> 'a monad -> 'a monad
  val throw : unit -> 'a monad

  val inEnv : MTS.var -> env -> bool
  val isFresh : MTS.var -> unit monad
  val trimEnv : MTS.var -> 'a monad -> 'a monad
  val bindAbsTerm : MTS.var -> MTS.term -> 'a monad -> 'a monad
  val bindManifestTerm : MTS.var -> MTS.term -> MTS.term -> 'a monad -> 'a monad
  val bindAbsMod : MTS.var -> MTS.modtype -> 'a monad -> 'a monad
  val bindManifestMod : MTS.var -> MTS.modtype -> MTS.modexpr -> 'a monad -> 'a monad
  val bindSpec : MTS.var -> MTS.specification -> 'a monad -> 'a monad
  val bindManySpec : ((MTS.var * MTS.var) * MTS.specification) list -> 'a monad -> 'a monad

  val registerSort : MTS.sort -> unit monad
  val registerAxiom : MTS.sort -> MTS.sort -> unit monad
  val registerRule : MTS.sort -> MTS.sort -> MTS.sort -> unit monad
  
  val getSorts : unit -> MTS.sorts monad
  val getAxioms : unit -> MTS.ax monad
  val getRules : unit -> MTS.rules monad

  val getSpec : MTS.var -> MTS.specification monad
  val getSpecType : MTS.specification -> MTS.term monad
  val getTy : MTS.var -> MTS.term monad
  val getSpecModtype : MTS.specification -> MTS.modtype monad
  val getModtype : MTS.var -> MTS.modtype monad
  val getDefModexpr : MTS.def -> MTS.modexpr monad
  val getDefTerm : MTS.def -> MTS.term monad
  val isLambda : MTS.term -> (MTS.var * MTS.term * MTS.term) monad
  val isDepProduct : MTS.term -> (MTS.var * MTS.term * MTS.term) monad
  val isBoolTy : MTS.term -> unit monad
  val isStruct : MTS.modexpr -> ((MTS.var * MTS.var) * MTS.def) list monad
  val isFunctor : MTS.modexpr -> (MTS.var * MTS.modtype * MTS.modexpr) monad
  val isSig : MTS.modtype
    -> ((MTS.var * MTS.var) * MTS.specification) list monad
  val isFuncT : MTS.modtype -> (MTS.var * MTS.modtype * MTS.modtype) monad
  val isTermTy : MTS.specification -> MTS.term monad

  val whstep : MTS.term -> MTS.term monad
  val whreduce : MTS.term -> MTS.term monad
  val nfstep : MTS.term -> MTS.term monad
  val nfreduce : MTS.term -> MTS.term monad
  val bequiv : MTS.term -> MTS.term -> unit monad

  val pseudoTModexpr : MTS.modexpr -> MTS.specification monad
  val pseudoTPath : MTS.path -> MTS.specification monad
  val mexprstep : MTS.modexpr -> MTS.modexpr monad
  val mexprreduce : MTS.modexpr -> MTS.modexpr monad
  val mequiv : MTS.modexpr -> MTS.modexpr -> unit monad

  val field : MTS.path -> ((MTS.var * MTS.var) * MTS.specification) list
    -> MTS.specification monad
end
=
struct
  type enventry = MTS.var * MTS.specification
  type env = enventry list
  type s = MTS.sorts * MTS.ax * MTS.rules
  structure M = StateFunctor (type s = s)
  structure MM = ReaderT (type s = env; structure M = M)
  structure MMM = ExceptionT (type e = unit; structure M = MM)
  structure MMMM = OptionT (structure M = MMM)
  structure Util = MUtil (structure M = MMMM)
  open MMMM
  open MTS

  val getstate = lift (MMM.lift (MM.lift M.get))

  val putstate = (fn st => lift (MMM.lift (MM.lift (M.put st))))

  val ask = lift (MMM.lift MM.ask)

  fun loc f m = (MM.loc f) m

  fun throw () = MMM.throw ()

  fun registerSort srt =
    getstate >>= (fn (srts, axs, rls) =>
    putstate (srt::srts, axs, rls))

  fun registerAxiom s1 s2 =
    getstate >>= (fn (srts, axs, rls) =>
    putstate (srts, (s1, s2)::axs, rls))

  fun registerRule s1 s2 s3 =
    getstate >>= (fn (srts, axs, rls) =>
    putstate (srts, axs, (s1, s2, s3)::rls))

  fun getSorts () =
    getstate >>= (fn (srts, axs, rls) => return srts)

  fun getAxioms () =
    getstate >>= (fn (srts, axs, rls) => return axs)

  fun getRules () =
    getstate >>= (fn (srts, axs, rls) => return rls)

  fun inEnv v e =
    List.exists (fn (v', x) => v = v') e

  fun isFresh v =
    ask >>= (fn e =>
    if inEnv v e then throw ()
    else return ())

  fun bindAbsTerm v m =
    loc (fn e => (v, SpecAbsTerm m)::e)

  fun bindManifestTerm v m1 m2 =
    loc (fn e => (v, SpecManifestTerm (m1, m2))::e)

  fun bindAbsMod v m =
    loc (fn e => (v, SpecAbsMod m)::e)

  fun bindManifestMod v m1 m2 =
    loc (fn e => (v, SpecManifestMod (m1, m2))::e)

  fun bindSpec v s =
    loc (fn e => (v, s)::e)

  fun bindManySpec ([]) m = m
  | bindManySpec (((v, v'), s)::xs) m =
    (bindSpec v s (bindManySpec xs m))

  fun getSpec v =
    ask >>= (fn e =>
      case List.find (fn (v', x) => v = v') e of
        SOME (_, s) => return s
      | NONE => throw ())

  fun trimEnv v =
    let
      fun f (e0) ([]) = raise Fail "should not happen if you checked"
      | f (e0) ((v', e)::e1) =
          if eqv v v' then List.rev e0
          else f ((v', e)::e0) e1
    in
      loc (f [])
    end

  fun getDefModexpr (DefVal m) = throw ()
  | getDefModexpr (DefData _) = raise Fail ""
  | getDefModexpr (DefMod m) = return m
  | getDefModexpr (DefModSig (m1, m2)) = return m1
  | getDefModexpr (DefModTransparent m) = return m

  fun getDefTerm (DefVal m) = return m
  | getDefTerm (DefData _) = raise Fail ""
  | getDefTerm (DefMod m) = throw ()
  | getDefTerm (DefModSig (m1, m2)) = throw ()
  | getDefTerm (DefModTransparent m) = throw ()

  fun isLambda (Lambda (v, m1, m2)) = return (v, m1, m2)
  | isLambda _ = throw ()

  fun isDepProduct (DepProduct (v, m1, m2)) = return (v, m1, m2)
  | isDepProduct _ = throw ()

  fun isBoolTy (Lit BoolTyLit) = return ()
  | isBoolTy _ = throw ()

  and isStruct (ModStruct s) = return s
  | isStruct _ = throw ()

  and isFunctor (ModFunctor (v, m1, m2)) = return (v, m1, m2)
  | isFunctor _ = throw ()

  fun getSpecType s =
    (case s of
      SpecAbsTerm m => return m
    | SpecManifestTerm (m, _) => return m
    | _ => throw ())

  fun getSpecModtype s =
    (case s of
      SpecAbsMod m => return m
    | SpecManifestMod (m, _) => return m
    | _ => throw ())

  fun getTy v =
    getSpec v >>= getSpecType

  fun getModtype p =
    getSpec p >>= getSpecModtype

  and isSig (ModTypeSig vsl) = return vsl
  | isSig _ = throw ()

  and isFuncT (ModTypeFunctor (v, m1, m2)) = return (v, m1, m2)
  | isFuncT _ = throw ()

  and isTermTy (SpecAbsTerm m) = return m
  | isTermTy (SpecManifestTerm (m, _)) = return m
  | isTermTy _ = throw ()

  fun nfstep (Path _) = zero ()
  | nfstep (Lit _) = zero ()
  | nfstep (Sort _) = zero ()
  | nfstep (App (m1, m2)) =
      (nfstep m1 >>= (fn m1' => return (App (m1', m2))))
      ++ (nfstep m2 >>= (fn m2' => return (App (m1, m2'))))
      ++ (isLambda m1 >>= (fn (v, m3, m4) => return (subst v m2 m4)))
  | nfstep (Case (m1, pml, m2)) = raise Fail ""
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
      ++ (isLambda m1 >>= (fn (v, m3, m4) => return (subst v m2 m4)))
  | whstep (Case (m1, pml, m2)) = raise Fail ""
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

  fun bequiv m1 m2 =
    nfreduce m1 >>= (fn m1' =>
    nfreduce m2 >>= (fn m2' =>
      if eq m1' m2' then return ()
      else throw ()))

  fun field _ ([]) = throw ()
  | field (PVar _) _ = throw ()
  | field (PPath (p, v)) (((x', _), s)::xs) =
      if eqv v x' then return s
      else field (PPath (p, v))
        (map (fn ((x'', x'''), s') => ((x'', x'''), PSub.substSpec x'
          (PPath (p, x')) s')) xs)

  fun pseudoTModexpr (ModStruct dl) =
      let
        fun f ([]) = return []
        | f (((v1, v2), d)::dl') =
            (case d of
              DefVal m => return (SpecManifestTerm (m, m))
            | DefData _ => raise Fail ""
            | DefMod m => pseudoTModexpr m
            | DefModSig (m1, m2) => return (SpecAbsMod m2)
            | DefModTransparent m => return (SpecManifestMod (ModTypeSig [], m))
            ) >>= (fn s =>
            bindSpec v2 s (f dl') >>= (fn sl =>
            return (((v1, v2), s)::sl)))
      in
        f dl >>= (fn sl =>
        return (SpecAbsMod (ModTypeSig sl)))
      end
  | pseudoTModexpr (ModFunctor (v, m1, m2)) =
      bindAbsMod v m1 (pseudoTModexpr m2) >>= (fn s =>
      getSpecModtype s >>= (fn m2' =>
      return (SpecAbsMod (ModTypeFunctor (v, m1, m2')))))
  | pseudoTModexpr (ModApp (m1, m2)) =
      pseudoTModexpr m1 >>= (fn s =>
      getSpecModtype s >>= (fn m1' =>
      isFuncT m1' >>= (fn (v, _, m3) =>
      return (SpecAbsMod (MSub.substModtype v m2 m3)))))
  | pseudoTModexpr (ModPath p) = pseudoTPath p
  and pseudoTPath (PVar v) = getSpec v
  | pseudoTPath (PPath (p, v)) =
      pseudoTModexpr p >>= (fn s =>
      getSpecModtype s >>= (fn s' =>
      isSig s' >>= (fn s'' =>
      field (PPath (p, v)) s'')))

  fun mexprstep (ModStruct dl) = throw ()
  | mexprstep (ModFunctor (v, m1, m2)) = throw ()
  | mexprstep (ModApp (m1, m2)) =
      (mexprstep m1 >>= (fn m1' => return (ModApp (m1', m2))))
      ++ (isFunctor m1 >>= (fn (v, m3, m4) => return (MSub.substModexpr v m2 m4)))
  | mexprstep (ModPath (PPath (p, v))) =
      (mexprstep p >>= (fn p' => return (ModPath (PPath (p', v)))))
      ++ (isStruct p >>= (fn dl =>
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
      ++ (pseudoTModexpr p >>= (fn s =>
        getSpecModtype s >>= (fn s' =>
        isSig s' >>= (fn s'' =>
        (case List.find (fn ((v', _), _) => eqv v v') s'' of
          SOME ((_, _), SpecManifestMod (_, m)) => return m
        | _ => throw ())))))
  | mexprstep (ModPath (PVar v)) = throw ()

  fun mexprreduce m =
    (mexprstep m >>= (fn m' => mexprreduce m')) ++ return m

  fun mequiv m1 m2 =
    mexprreduce m1 >>= (fn m1' =>
    mexprreduce m2 >>= (fn m2' =>
      if mexpreq m1' m2' then return ()
      else throw ()))

end


