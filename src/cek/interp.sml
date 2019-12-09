structure Interp : sig
  datatype environment = 
    EmptyEnv
  | Env of Lang.var * Lang.value * environment

  datatype heapvalue = 
    HeapIntLit of int
  | HeapBoolLit of bool
  | HeapUnitLit
  | HeapLambda of Lang.var * Lang.term * Lang.ty
  | HeapRegionLambda of Lang.regionvar * Lang.abs
  | HeapTuple of Lang.term * Lang.term
  | HeapBarePointer of Lang.regionvar * Lang.pointername

  type region = heapvalue list
  type store = (Lang.regionvar * region) list

  datatype continuation =
    Empty
  | AR of Lang.term * environment * continuation
  | PR1 of Lang.operator * Lang.term * environment * continuation
  | PR2 of Lang.operator * Lang.term * environment * continuation
  | CALL of Lang.var * Lang.term * environment * continuation
  | LT of Lang.var * Lang.ty * Lang.term * environment * continuation
  | IF of Lang.term * Lang.term * environment * continuation
  | TUP1 of Lang.regionvar * Lang.term * environment * continuation
  | TUP2 of Lang.regionvar * Lang.term * environment * continuation
  | FST of environment * continuation
  | SND of environment * continuation
  | BX of Lang.regionvar * environment * continuation
  | UNBX of environment * continuation
  | FREERGN of Lang.regionvar * environment * continuation
  | ELIM of Lang.regionvar * environment * continuation

  type state = Lang.term * environment * store * continuation

  val lookup : Lang.var * environment -> Lang.value
  val removeRegion : (Lang.regionvar * store) -> store
  val doOperation : (Lang.operator * Lang.term * Lang.term) -> Lang.term
  val step : state -> state
  val runToCompletion : state -> state
end
=
struct
  open Lang

  datatype environment = 
    EmptyEnv
  | Env of var * value * environment

  datatype heapvalue = 
    HeapIntLit of int
  | HeapBoolLit of bool
  | HeapUnitLit
  | HeapLambda of Lang.var * Lang.term * Lang.ty
  | HeapRegionLambda of Lang.regionvar * Lang.abs
  | HeapTuple of term * term
  | HeapBarePointer of regionvar * pointername

  type region = heapvalue list
  type store = (regionvar * region) list

  datatype continuation =
    Empty
  | AR of term * environment * continuation
  | PR1 of operator * term * environment * continuation
  | PR2 of operator * term * environment * continuation
  | CALL of var * term * environment * continuation
  | LT of var * ty * term * environment * continuation
  | IF of term * term * environment * continuation
  | TUP1 of regionvar * term * environment * continuation
  | TUP2 of regionvar * term * environment * continuation
  | FST of environment * continuation
  | SND of environment * continuation
  | BX of regionvar * environment * continuation
  | UNBX of environment * continuation
  | FREERGN of regionvar * environment * continuation
  | ELIM of regionvar * environment * continuation

  type state = term * environment * store * continuation

  fun lookup (v : var, EmptyEnv) = raise Fail "var not in env"
  | lookup (v, Env (v', mv, e)) =
      if v = v' then mv
      else lookup (v, e)

  fun removeRegion (r, []) = []
  | removeRegion (r, (rn, reg)::s) =
      if r = rn then s
      else (rn, reg)::(removeRegion (r, s))

  fun doOperation (opr, m1, m2) =
    (case (m1, m2) of
      (Value (IntLit i1), Value (IntLit i2)) =>
        (case opr of
          "+" => Value (IntLit (i1 + i2))
        | "-" => Value (IntLit (i1 - i2))
        | "*" => Value (IntLit (i1 * i2))
        | "<" => Value (BoolLit (i1 < i2))
        | "=" => Value (BoolLit (i1 = i2))
        | _ => raise Fail "undefined operator"
        )
    | _ => raise Fail "cannot do prim op on these types"
    )

  fun step (c : term, e : environment, s : store, k : continuation) : state = 
    let 
      fun makeHeapValue (BoxIntLit (i, r)) = (r, HeapIntLit i)
      | makeHeapValue (BoxBoolLit (b, r)) = (r, HeapBoolLit b)
      | makeHeapValue (BoxUnitLit r) = (r, HeapUnitLit)
      | makeHeapValue (BoxAbs (Lambda (x, m, argt, r))) = (r, HeapLambda (x, m, argt))
      | makeHeapValue (BoxAbs (RegionLambda (r, a, r2))) = (r2, HeapRegionLambda (r, a))
      | makeHeapValue (BoxTuple (m1, m2, r)) = (r, HeapTuple (m1, m2))
      | makeHeapValue (BoxBarePointer (r, p, r2)) = (r2, HeapBarePointer (r, p))

      fun putStore (bv : boxvalue, s : store) : (regionvar * pointername) * store = 
        let val (r, v) = makeHeapValue bv
        in
          case List.partition (fn (x, _) => x = r) s of
            ([], s') => ((r, 0), (r, [v])::s')
          | ([(rn, reg)], s') => ((r, List.length reg), (r, reg @ [v])::s')
          | _ => raise Fail "duplicate region name"
        end
    in
      (case c of
        Value (IntLit i) =>
          (case k of
            Empty => (c, e, s, k)
          | AR (m', e', k') => raise Fail "irrelevant continuation"
          | PR1 (opr, m, e', k') => (m, e', s, PR2 (opr, c, e', k'))
          | PR2 (opr, m, e', k') => (doOperation (opr, m, c), e', s, k')
          | CALL (x', m', e', k') => (m', Env (x', IntLit i, e'), s, k')
          | LT (x', argt', m', e', k') => (m', Env (x', IntLit i, e'), s, k')
          | IF (m1, m2, e', k') => raise Fail "irrelevant continuation"
          | TUP1 (r, m', e', k') => (m', e', s, TUP2 (r, c, e', k'))
          | TUP2 (r, m', e', k') => (BoxedValue (BoxTuple (m', c, r)), e', s, k')
          | FST (e', k') => raise Fail "irrelevant continuation"
          | SND (e', k') => raise Fail "irrelevant continuation"
          | BX (r, e', k') =>
              let val (p, s') = putStore (BoxIntLit (i, r), s)
              in
                (Lang.Value (Lang.BarePointer p), e', s', k')
              end
          | UNBX (e', k') => raise Fail "irrelevant continuation"
          | FREERGN (r, e', k') => (c, e', removeRegion (r, s), k')
          | ELIM (r, e', k') => raise Fail "irrelevant continuation"
          )
      | Value (BoolLit b) =>
          (case k of
            Empty => (c, e, s, k)
          | AR (m', e', k') => raise Fail "irrelevant continuation"
          | PR1 (opr, m, e', k') => (m, e', s, PR2 (opr, c, e', k'))
          | PR2 (opr, m, e', k') => (doOperation (opr, m, c), e', s, k')
          | CALL (x', m', e', k') => (m', Env (x', BoolLit b, e'), s, k')
          | LT (x', argt', m', e', k') => (m', Env (x', BoolLit b, e'), s, k')
          | IF (m1, m2, e', k') => 
              if b then (m1, e', s, k')
              else (m2, e', s, k')
          | TUP1 (r, m', e', k') => (m', e', s, TUP2 (r, c, e', k'))
          | TUP2 (r, m', e', k') => (BoxedValue (BoxTuple (m', c, r)), e', s, k')
          | FST (e', k') => raise Fail "irrelevant continuation"
          | SND (e', k') => raise Fail "irrelevant continuation"
          | BX (r, e', k') =>
              let val (p, s') = putStore (BoxBoolLit (b, r), s)
              in
                (Lang.Value (Lang.BarePointer p), e', s', k')
              end
          | UNBX (e', k') => raise Fail "irrelevant continuation"
          | FREERGN (r, e', k') => (c, e', removeRegion (r, s), k')
          | ELIM (r, e', k') => raise Fail "irrelevant continuation"
          )
      | Value (UnitLit) =>
          (case k of
            Empty => (c, e, s, k)
          | AR (m', e', k') => raise Fail "irrelevant continuation"
          | PR1 (opr, m, e', k') => raise Fail "irrelevant continuation"
          | PR2 (opr, m, e', k') => raise Fail "irrelevant continuation"
          | CALL (x', m', e', k') => (m', Env (x', UnitLit, e'), s, k')
          | LT (x', argt', m', e', k') => (m', Env (x', UnitLit, e'), s, k')
          | IF (m1, m2, e', k') => raise Fail "irrelevant continuation"
          | TUP1 (r, m', e', k') => (m', e', s, TUP2 (r, c, e', k'))
          | TUP2 (r, m', e', k') => (BoxedValue (BoxTuple (m', c, r)), e', s, k')
          | FST (e', k') => raise Fail "irrelevant continuation"
          | SND (e', k') => raise Fail "irrelevant continuation"
          | BX (r, e', k') =>
              let val (p, s') = putStore (BoxUnitLit r, s)
              in
                (Lang.Value (Lang.BarePointer p), e', s', k')
              end
          | UNBX (e', k') => raise Fail "irrelevant continuation"
          | FREERGN (r, e', k') => (c, e', removeRegion (r, s), k')
          | ELIM (r, e', k') => raise Fail "irrelevant continuation"
          )
      | Value (Tuple (m1, m2)) => 
          (case k of
            Empty => (c, e, s, k)
          | AR (m', e', k') => raise Fail "irrelevant continuation"
          | PR1 (opr, m, e', k') => raise Fail "irrelevant continuation"
          | PR2 (opr, m, e', k') => raise Fail "irrelevant continuation"
          | CALL (x', m', e', k') => (m', Env (x', Tuple (m1, m2), e'), s, k')
          | LT (x', argt', m', e', k') => (m', Env (x', Tuple (m1, m2), e'), s, k')
          | IF (m1, m2, e', k') => raise Fail "irrelevant continuation"
          | TUP1 (r, m', e', k') => (m', e', s, TUP2 (r, c, e', k'))
          | TUP2 (r, m', e', k') => (BoxedValue (BoxTuple (m', c, r)), e', s, k')
          | FST (e', k') => raise Fail "irrelevant continuation"
          | SND (e', k') => raise Fail "irrelevant continuation"
          | BX (r, e', k') => 
              let val (p, s') = putStore (BoxTuple (m1, m2, r), s)
              in
                (Lang.Value (Lang.BarePointer p), e', s', k')
              end
          | UNBX (e', k') => raise Fail "irrelevant continuation"
          | FREERGN (r, e', k') => (c, e', removeRegion (r, s), k')
          | ELIM (r, e', k') => raise Fail "irrelevant continuation"
          )
      | Value (BarePointer (r, p)) =>
          (case List.find (fn (x, _) => x = r) s of
            SOME (rn, mv) => 
              (case k of
                Empty => (c, e, s, k)
              | AR (m', e', k') => 
                  (case List.nth (mv, p) of
                    HeapIntLit i => raise Fail "cannot AR boxint"
                  | HeapBoolLit b => raise Fail "cannot AR boxbool"
                  | HeapUnitLit => raise Fail "cannot AR boxunit"
                  | HeapLambda (x, m, argt) => (m', e', s, CALL (x, m, e, k'))
                  | HeapRegionLambda (r2, a) => raise Fail "cannot AR boxreglambda"
                  | HeapTuple (m1, m2) => raise Fail "cannot AR boxtuple"
                  | HeapBarePointer (r, p) => raise Fail "cannot AR bp"
                  )
              | PR1 (opr, m, e', k') => raise Fail "irrelevant continuation"
              | PR2 (opr, m, e', k') => raise Fail "irrelevant continuation"
              | CALL (x', m', e', k') => (m', Env (x', BarePointer (r, p), e'), s, k')
              | LT (x', argt', m', e', k') => (m', Env (x', BarePointer (r, p), e'), s, k')
              | IF (m1, m2, e', k') => raise Fail "irrelevant continuation"
              | TUP1 (r, m', e', k') => (m', e', s, TUP2 (r, c, e', k'))
              | TUP2 (r, m', e', k') => (BoxedValue (BoxTuple (m', c, r)), e', s, k')
              | FST (e', k') => 
                  (case List.nth (mv, p) of
                    HeapIntLit i => raise Fail "cannot fst boxint"
                  | HeapBoolLit b => raise Fail "cannot fst boxbool"
                  | HeapUnitLit => raise Fail "cannot fst boxunit"
                  | HeapLambda (x, m, argt) => raise Fail "cannot fst boxlambda"
                  | HeapRegionLambda (r2, a) => raise Fail "cannot fst boxreglambda"
                  | HeapTuple (m1, m2) => (m1, e', s, k')
                  | HeapBarePointer (r, p) => raise Fail "cannot fst boxabs"
                  )
              | SND (e', k') => 
                  (case List.nth (mv, p) of
                    HeapIntLit i => raise Fail "cannot snd boxint"
                  | HeapBoolLit b => raise Fail "cannot snd boxbool"
                  | HeapUnitLit => raise Fail "cannot snd boxunit"
                  | HeapLambda (x, m, argt) => raise Fail "cannot snd boxlambda"
                  | HeapRegionLambda (r2, a) => raise Fail "cannot snd boxreglambda"
                  | HeapTuple (m1, m2) => (m2, e', s, k')
                  | HeapBarePointer (r, p) => raise Fail "cannot snd boxabs"
                  )
              | BX (r2, e', k') => 
                  let val (p, s') = putStore (BoxBarePointer (r, p, r2), s)
                  in
                    (Lang.Value (Lang.BarePointer p), e', s', k')
                  end
              | UNBX (e', k') => 
                  (case List.nth (mv, p) of
                    HeapIntLit i => (Value (IntLit i), e, s, k)
                  | HeapBoolLit b => (Value (BoolLit b), e, s, k)
                  | HeapUnitLit => (Value (UnitLit), e, s, k)
                  | HeapLambda (x, m, argt) => raise Fail "cannot unbox boxlambda"
                  | HeapRegionLambda (r2, a) => raise Fail "cannot unbox boxreglambda"
                  | HeapTuple (m1, m2) => raise Fail "cannot unbox tuple"
                  | HeapBarePointer (r, p) => (Value (BarePointer (r, p)), e, s, k)
                  )
              | FREERGN (r, e', k') => (c, e', removeRegion (r, s), k')
              | ELIM (r1, e', k') => 
                  (case List.nth (mv, p) of
                    HeapIntLit i => raise Fail "cannot elim boxint"
                  | HeapBoolLit b => raise Fail "cannot elim boxbool"
                  | HeapUnitLit => raise Fail "cannot elim boxunit"
                  | HeapLambda (x, m, argt) => raise Fail "cannot elim boxlambda"
                  | HeapRegionLambda (r2, a) => (BoxedValue (BoxAbs (substRegVarAbs (r2, r1) a)), e', s, k')
                  | HeapTuple (m1, m2) => raise Fail "cannot elim boxtuple"
                  | HeapBarePointer (r, p) => raise Fail "cannot elim boxabs"
                  )
              )
          | NONE => raise Fail "unknown region")
      | BoxedValue v => 
          let val (bp, s')  = putStore (v, s)
          in
            (Value (BarePointer bp), e, s', k)
          end
      | Var v => (Value (lookup (v, e)), e, s, k)
      | First (m) => (m, e, s, FST (e, k))
      | Second (m) => (m, e, s, SND (e, k))
      | Unbox (m) => (m, e, s, UNBX (e, k))
      | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
      | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
      | RegionElim (m, r) => (m, e, s, ELIM (r, e, k))
      | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
      | App (m1, m2) => (m1, e, s, AR (m2, e, k))
      | PrimApp (opr, m1, m2) => (m1, e, s, PR1 (opr, m2, e, k))
      )
    end

  fun runToCompletion (c : term, e : environment, s : store, k : continuation) : state = 
    if isValue c then
      (case k of
        Empty => (c, e, s, k)
      | _ => runToCompletion (step (c, e, s, k)))
    else runToCompletion (step (c, e, s, k))
end

