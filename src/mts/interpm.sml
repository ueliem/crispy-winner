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

  val registerSort : MTS.sort -> unit monad
  val registerAxiom : MTS.sort -> MTS.sort -> unit monad
  val registerRule : MTS.sort -> MTS.sort -> MTS.sort -> unit monad
  
  val getSorts : unit -> MTS.sorts monad
  val getAxioms : unit -> MTS.ax monad
  val getRules : unit -> MTS.rules monad

  val getTy : MTS.var -> MTS.term monad
  val getSpec : MTS.var -> MTS.specification monad
  val isLambda : MTS.term -> (MTS.var * MTS.term * MTS.term) monad
  val isDepProduct : MTS.term -> (MTS.var * MTS.term * MTS.term) monad
  val isBoolTy : MTS.term -> unit monad
  val getModtype : MTS.var -> MTS.modtype monad
  val isSig : MTS.specification -> (MTS.var * MTS.specification) list monad
  val isFuncT : MTS.specification -> (MTS.var * MTS.modtype * MTS.modtype) monad
  val isTermTy : MTS.specification -> MTS.term monad

  val whstep : MTS.term -> MTS.term monad
  val whreduce : MTS.term -> MTS.term monad
  val nfstep : MTS.term -> MTS.term monad
  val nfreduce : MTS.term -> MTS.term monad
  val bequiv : MTS.term -> MTS.term -> unit monad

  val field : MTS.path -> (MTS.var * MTS.specification) list -> MTS.specification monad
  (* val resolvePath : MTS.path -> MTS.specification monad
  val pathHead : MTS.path -> MTS.var *)
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

  fun getTy v =
    ask >>= (fn e =>
      case List.find (fn (v', x) => v = v') e of
        SOME (_, SpecAbsMod _) => throw ()
      | SOME (_, SpecManifestMod _) => throw ()
      | SOME (_, SpecAbsTerm m) => return m
      | SOME (_, SpecManifestTerm (m, _)) => return m
      | NONE => throw ())

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

  fun isLambda (Lambda (v, m1, m2)) = return (v, m1, m2)
  | isLambda _ = throw ()

  fun isDepProduct (DepProduct (v, m1, m2)) = return (v, m1, m2)
  | isDepProduct _ = throw ()

  fun isBoolTy (Lit BoolTyLit) = return ()
  | isBoolTy _ = throw ()

  fun getModtype p =
    getSpec p >>= (fn s => (case s of
      SpecAbsMod m => return m
    | SpecManifestMod (m, _) => return m
    | _ => throw ()))

  and isSig (SpecAbsMod (ModTypeSig vsl)) = return vsl
  | isSig (SpecManifestMod (ModTypeSig vsl, _)) = return vsl
  | isSig _ = throw ()

  and isFuncT (SpecAbsMod (ModTypeFunctor (v, m1, m2))) = return (v, m1, m2)
  | isFuncT (SpecManifestMod (ModTypeFunctor (v, m1, m2), _)) = return (v, m1, m2)
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
  | field (PPath (p, v)) ((x', s)::xs) =
      if eqv v x' then return s
      else field (PPath (p, v)) (map (fn (x'', s') => (x'', substSpec x'
        (Path (PPath (p, x'))) s')) xs)

  (* fun pathHead (PVar v) = v
  | pathHead (PPath (p, _)) = pathHead p

  fun resolvePath (PVar v) = getSpec v
  | resolvePath (PPath (p, v)) =
      resolvePath p >>= (fn s =>
      isSig s >>= (fn s' =>
      (case List.find (fn (x, _) => eqv v x) s' of
        SOME (_, s) => return s
      | NONE => throw ())))
  | resolvePath (PFunc (p1, p2)) =
      resolvePath p1 >>= (fn s1 =>
      isFuncT s1 >>= (fn (v, m1, m2) =>
      bindAbsMod v m1 (resolvePath p2) >>= (fn _ =>
        return (SpecAbsMod (substModtype v (Path p2) m2))))) *)

end


