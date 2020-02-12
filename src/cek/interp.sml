structure Interp : sig
  datatype environment = 
    EmptyEnv
  | Env of Lang.var * Lang.value * environment

  datatype heapvalue = 
    HeapIntLit of int
  | HeapBoolLit of bool
  | HeapUnitLit
  | HeapLambda of Lang.var list * Lang.term * Lang.ty list
  | HeapRegionLambda of Lang.regionvar * Lang.abs
  | HeapTuple of Lang.value list
  | HeapBarePointer of Lang.regionvar * Lang.pointername

  type region = heapvalue list
  type store = (Lang.regionvar * region) list

  datatype continuation =
    Empty
  | AR of Lang.term list * environment * continuation
  | PR1 of Lang.operator * Lang.term * environment * continuation
  | PR2 of Lang.operator * Lang.term * environment * continuation
  | CALL of Lang.var list * Lang.term * Lang.term list * Lang.value list * environment * continuation
  | LT of Lang.var * Lang.ty * Lang.term * environment * continuation
  | IF of Lang.term * Lang.term * environment * continuation
  | TUP of Lang.regionvar * Lang.term list * Lang.value list * environment * continuation
  | SEL of int * environment * continuation
  | BX of Lang.regionvar * environment * continuation
  | UNBX of environment * continuation
  | FREERGN of Lang.regionvar * environment * continuation
  | ELIM of Lang.regionvar * Lang.regionvar * environment * continuation

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
  | HeapLambda of Lang.var list * Lang.term * Lang.ty list
  | HeapRegionLambda of Lang.regionvar * Lang.abs
  | HeapTuple of Lang.value list
  | HeapBarePointer of regionvar * pointername

  type region = heapvalue list
  type store = (regionvar * region) list

  datatype continuation =
    Empty
  | AR of term list * environment * continuation
  | PR1 of operator * term * environment * continuation
  | PR2 of operator * term * environment * continuation
  | CALL of Lang.var list * Lang.term * Lang.term list * Lang.value list * environment * continuation
  | LT of var * ty * term * environment * continuation
  | IF of term * term * environment * continuation
  | TUP of Lang.regionvar * Lang.term list * Lang.value list * environment * continuation
  | SEL of int * environment * continuation
  | BX of regionvar * environment * continuation
  | UNBX of environment * continuation
  | FREERGN of regionvar * environment * continuation
  | ELIM of regionvar * regionvar * environment * continuation

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
      fun putStore (r : regionvar, v : heapvalue, s : store) : (regionvar * pointername) * store = 
        case List.partition (fn (x, _) => x = r) s of
          ([], s') => ((r, 0), (r, [v])::s')
        | ([(rn, reg)], s') => ((r, List.length reg), (r, reg @ [v])::s')
        | _ => raise Fail "duplicate region name"

      fun boxValue (e : environment, s : store, k : continuation) (v : Lang.boxvalue) : state = 
        (case v of 
          BoxIntLit (i, r) => 
            let val (bp, s')  = putStore (r, HeapIntLit i, s)
            in
              (Value (BarePointer bp), e, s', k)
            end
        | BoxBoolLit (b, r) => 
            let val (bp, s')  = putStore (r, HeapBoolLit b, s)
            in
              (Value (BarePointer bp), e, s', k)
            end
        | BoxUnitLit r => 
            let val (bp, s')  = putStore (r, HeapUnitLit, s)
            in
              (Value (BarePointer bp), e, s', k)
            end
        | BoxAbs (Lambda (x, m, argt, r)) => 
            let val (bp, s')  = putStore (r, HeapLambda (x, m, argt), s)
            in
              (Value (BarePointer bp), e, s', k)
            end
        | BoxAbs (RegionLambda (r1, m, r2)) => 
            let val (bp, s')  = putStore (r2, HeapRegionLambda (r1, m), s)
            in
              (Value (BarePointer bp), e, s', k)
            end
        | BoxTuple ([], r) => raise Fail "not possible"
        | BoxTuple (m::ms, r) => 
            (m, e, s, TUP (r, ms, [], e, k))
        | BoxBarePointer (r1, p, r2) => 
            let val (bp, s')  = putStore (r2, HeapBarePointer (r1, p), s)
            in
              (Value (BarePointer bp), e, s', k)
            end
        )

        fun extendEnv e [] = e
        | extendEnv e ((x, v)::vl) = extendEnv (Env (x, v, e)) vl
    in
        (case k of
          Empty => 
            (case c of 
              Value (IntLit i) => (c, e, s, k)
            | Value (BoolLit b) => (c, e, s, k)
            | Value (UnitLit) => (c, e, s, k)
            | Value (BarePointer (r, p)) => (c, e, s, k)
            | BoxedValue v => boxValue (e, s, k) v
            | Var v => (Value (lookup (v, e)), e, s, k)
            | Select (i, m) => (m, e, s, SEL (i, e, k))
            | Unbox (m) => (m, e, s, UNBX (e, k))
            | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
            | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
            | RegionElim (f, r1, r2) => (Var f, e, s, ELIM (r1, r2, e, k))
            | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
            | App (m1, m2) => (m1, e, s, AR (m2, e, k))
            | PrimApp (opr, m1, m2) => (m1, e, s, PR1 (opr, m2, e, k))
            )
        | AR ([], e', k') => raise Fail "not possible"
        | AR (m'::ms', e', k') => 
            (case c of 
              Value (IntLit i) => raise Fail "irrelevant continuation"
            | Value (BoolLit b) => raise Fail "irrelevant continuation"
            | Value (UnitLit) => raise Fail "irrelevant continuation"
            | Value (BarePointer (r, p)) =>
                (case List.find (fn (x, _) => x = r) s of
                  SOME (rn, mv) => 
                    (case List.nth (mv, p) of
                      HeapIntLit i => raise Fail "cannot AR boxint"
                    | HeapBoolLit b => raise Fail "cannot AR boxbool"
                    | HeapUnitLit => raise Fail "cannot AR boxunit"
                    | HeapLambda (x, m, argt) => (m', e', s, CALL (x, m, ms', [], e, k'))
                    | HeapRegionLambda (r2, a) => raise Fail "cannot AR boxreglambda"
                    | HeapTuple (m) => raise Fail "cannot AR boxtuple"
                    | HeapBarePointer (r, p) => raise Fail "cannot AR bp"
                    )
                | NONE => raise Fail "unknown region"
                )
            | BoxedValue v => boxValue (e, s, k) v
            | Var v => (Value (lookup (v, e)), e, s, k)
            | Select (i, m) => (m, e, s, SEL (i, e, k))
            | Unbox (m) => (m, e, s, UNBX (e, k))
            | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
            | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
            | RegionElim (f, r1, r2) => (Var f, e, s, ELIM (r1, r2, e, k))
            | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
            | App (m1, m2) => (m1, e, s, AR (m2, e, k))
            | PrimApp (opr, m1, m2) => (m1, e, s, PR1 (opr, m2, e, k))
            )
        | PR1 (opr, m, e', k') => 
            (case c of 
              Value (IntLit i) => (m, e', s, PR2 (opr, c, e', k'))
            | Value (BoolLit b) => (m, e', s, PR2 (opr, c, e', k'))
            | Value (UnitLit) => raise Fail "irrelevant continuation"
            | Value (BarePointer (r, p)) => raise Fail "irrelevant continuation"
            | BoxedValue v => raise Fail "irrelevant continuation"
            | Var v => (Value (lookup (v, e)), e, s, k)
            | Select (i, m) => (m, e, s, SEL (i, e, k))
            | Unbox (m) => (m, e, s, UNBX (e, k))
            | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
            | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
            | RegionElim (f, r1, r2) => (Var f, e, s, ELIM (r1, r2, e, k))
            | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
            | App (m1, m2) => (m1, e, s, AR (m2, e, k))
            | PrimApp (opr, m1, m2) => (m1, e, s, PR1 (opr, m2, e, k))
            )
        | PR2 (opr, m, e', k') => 
            (case c of 
              Value (IntLit i) => (doOperation (opr, m, c), e', s, k')
            | Value (BoolLit b) => (doOperation (opr, m, c), e', s, k')
            | Value (UnitLit) => raise Fail "irrelevant continuation"
            | Value (BarePointer (r, p)) => raise Fail "irrelevant continuation"
            | BoxedValue v => raise Fail "irrelevant continuation"
            | Var v => (Value (lookup (v, e)), e, s, k)
            | Select (i, m) => (m, e, s, SEL (i, e, k))
            | Unbox (m) => (m, e, s, UNBX (e, k))
            | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
            | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
            | RegionElim (f, r1, r2) => (Var f, e, s, ELIM (r1, r2, e, k))
            | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
            | App (m1, m2) => (m1, e, s, AR (m2, e, k))
            | PrimApp (opr, m1, m2) => (m1, e, s, PR1 (opr, m2, e, k))
            )
        | CALL (x, m, m1, m2, e', k') => 
            (case c of 
              Value v => 
                (case m1 of
                  [] => (m, extendEnv e' (ListPair.zip (x, m2 @ [v])), s, k')
                | m'::ms => (m', e', s, CALL (x, m, ms, m2 @ [v], e', k')))
            | BoxedValue v => boxValue (e, s, k) v
            | Var v => (Value (lookup (v, e)), e, s, k)
            | Select (i, m) => (m, e, s, SEL (i, e, k))
            | Unbox (m) => (m, e, s, UNBX (e, k))
            | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
            | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
            | RegionElim (f, r1, r2) => (Var f, e, s, ELIM (r1, r2, e, k))
            | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
            | App (m1, m2) => (m1, e, s, AR (m2, e, k))
            | PrimApp (opr, m1, m2) => (m1, e, s, PR1 (opr, m2, e, k))
            )
        | LT (x', argt', m', e', k') => 
            (case c of 
              Value (IntLit i) => (m', Env (x', IntLit i, e'), s, k')
            | Value (BoolLit b) => (m', Env (x', BoolLit b, e'), s, k')
            | Value (UnitLit) => (m', Env (x', UnitLit, e'), s, k')
            | Value (BarePointer (r, p)) => (m', Env (x', BarePointer (r, p), e'), s, k')
            | BoxedValue v => boxValue (e, s, k) v
            | Var v => (Value (lookup (v, e)), e, s, k)
            | Select (i, m) => (m, e, s, SEL (i, e, k))
            | Unbox (m) => (m, e, s, UNBX (e, k))
            | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
            | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
            | RegionElim (f, r1, r2) => (Var f, e, s, ELIM (r1, r2, e, k))
            | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
            | App (m1, m2) => (m1, e, s, AR (m2, e, k))
            | PrimApp (opr, m1, m2) => (m1, e, s, PR1 (opr, m2, e, k))
            )
        | IF (m1, m2, e', k') => 
            (case c of 
              Value (IntLit i) => raise Fail "irrelevant continuation"
            | Value (BoolLit b) =>
                if b then (m1, e', s, k')
                else (m2, e', s, k')
            | Value (UnitLit) => raise Fail "irrelevant continuation"
            | Value (BarePointer (r, p)) => raise Fail "irrelevant continuation"
            | BoxedValue v => raise Fail "irrelevant continuation"
            | Var v => (Value (lookup (v, e)), e, s, k)
            | Select (i, m) => (m, e, s, SEL (i, e, k))
            | Unbox (m) => (m, e, s, UNBX (e, k))
            | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
            | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
            | RegionElim (f, r1, r2) => (Var f, e, s, ELIM (r1, r2, e, k))
            | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
            | App (m1, m2) => (m1, e, s, AR (m2, e, k))
            | PrimApp (opr, m1, m2) => (m1, e, s, PR1 (opr, m2, e, k))
            )
        | TUP (r, m1, m2, e', k') => 
            (case c of 
              Value v => 
                (case m1 of
                  [] => 
                    let val (bp, s')  = putStore (r, HeapTuple (m2 @ [v]), s)
                    in
                      (Value (BarePointer bp), e', s', k')
                    end
                | x::xs => (x, e', s, TUP (r, xs, m2 @ [v], e', k')))
            | BoxedValue v => boxValue (e, s, k) v
            | Var v => (Value (lookup (v, e)), e, s, k)
            | Select (i, m) => (m, e, s, SEL (i, e, k))
            | Unbox (m) => (m, e, s, UNBX (e, k))
            | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
            | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
            | RegionElim (f, r1, r2) => (Var f, e, s, ELIM (r1, r2, e, k))
            | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
            | App (m1, m2) => (m1, e, s, AR (m2, e, k))
            | PrimApp (opr, m1, m2) => (m1, e, s, PR1 (opr, m2, e, k))
            )
        | SEL (i, e', k') => 
            (case c of 
              Value (IntLit i) => raise Fail "irrelevant continuation"
            | Value (BoolLit b) => raise Fail "irrelevant continuation"
            | Value (UnitLit) => raise Fail "irrelevant continuation"
            | Value (BarePointer (r, p)) => 
                (case List.find (fn (x, _) => x = r) s of
                  SOME (rn, mv) => 
                    (case List.nth (mv, p) of
                      HeapIntLit i => raise Fail "cannot sel boxint"
                    | HeapBoolLit b => raise Fail "cannot sel boxbool"
                    | HeapUnitLit => raise Fail "cannot sel boxunit"
                    | HeapLambda (x, m, argt) => raise Fail "cannot sel boxlambda"
                    | HeapRegionLambda (r2, a) => raise Fail "cannot sel boxreglambda"
                    | HeapTuple (m) => (Value (List.nth (m, i)), e', s, k')
                    | HeapBarePointer (r, p) => raise Fail "cannot sel boxabs"
                    )
                | NONE => raise Fail "unknown region")
            | BoxedValue v => boxValue (e, s, k) v
            | Var v => (Value (lookup (v, e)), e, s, k)
            | Select (i, m) => (m, e, s, SEL (i, e, k))
            | Unbox (m) => (m, e, s, UNBX (e, k))
            | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
            | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
            | RegionElim (f, r1, r2) => (Var f, e, s, ELIM (r1, r2, e, k))
            | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
            | App (m1, m2) => (m1, e, s, AR (m2, e, k))
            | PrimApp (opr, m1, m2) => (m1, e, s, PR1 (opr, m2, e, k))
            )
        | BX (r, e', k') =>
            (case c of 
              Value (IntLit i) => 
                let val (bp, s')  = putStore (r, HeapIntLit i, s)
                in
                  (Value (BarePointer bp), e', s', k')
                end
            | Value (BoolLit b) => 
                let val (bp, s')  = putStore (r, HeapBoolLit b, s)
                in
                  (Value (BarePointer bp), e', s', k')
                end
            | Value (UnitLit) => 
                let val (bp, s')  = putStore (r, HeapUnitLit, s)
                in
                  (Value (BarePointer bp), e', s', k')
                end
            | Value (BarePointer (r1, p)) => 
                let val (bp, s')  = putStore (r, HeapBarePointer (r1, p), s)
                in
                  (Value (BarePointer bp), e', s', k')
                end
            | BoxedValue v => boxValue (e, s, k) v
            | Var v => (Value (lookup (v, e)), e, s, k)
            | Select (i, m) => (m, e, s, SEL (i, e, k))
            | Unbox (m) => (m, e, s, UNBX (e, k))
            | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
            | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
            | RegionElim (f, r1, r2) => (Var f, e, s, ELIM (r1, r2, e, k))
            | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
            | App (m1, m2) => (m1, e, s, AR (m2, e, k))
            | PrimApp (opr, m1, m2) => (m1, e, s, PR1 (opr, m2, e, k))
            )
        | UNBX (e', k') => 
            (case c of 
              Value (IntLit i) => raise Fail "irrelevant continuation"
            | Value (BoolLit b) => raise Fail "irrelevant continuation"
            | Value (UnitLit) => raise Fail "irrelevant continuation"
            | Value (BarePointer (r, p)) => 
                (case List.find (fn (x, _) => x = r) s of
                  SOME (rn, mv) => 
                    (case List.nth (mv, p) of
                      HeapIntLit i => (Value (IntLit i), e', s, k')
                    | HeapBoolLit b => (Value (BoolLit b), e', s, k')
                    | HeapUnitLit => (Value (UnitLit), e', s, k')
                    | HeapLambda (x, m, argt) => raise Fail "cannot unbox boxlambda"
                    | HeapRegionLambda (r2, a) => raise Fail "cannot unbox boxreglambda"
                    | HeapTuple (m) => raise Fail "cannot unbox tuple"
                    | HeapBarePointer (r, p) => (Value (BarePointer (r, p)), e', s, k')
                    )
                | NONE => raise Fail "unknown region"
                )
            | BoxedValue v => boxValue (e, s, k) v
            | Var v => (Value (lookup (v, e)), e, s, k)
            | Select (i, m) => (m, e, s, SEL (i, e, k))
            | Unbox (m) => (m, e, s, UNBX (e, k))
            | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
            | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
            | RegionElim (f, r1, r2) => (Var f, e, s, ELIM (r1, r2, e, k))
            | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
            | App (m1, m2) => (m1, e, s, AR (m2, e, k))
            | PrimApp (opr, m1, m2) => (m1, e, s, PR1 (opr, m2, e, k))
            )
        | FREERGN (r, e', k') => 
            (case c of 
              Value v => (c, e', removeRegion (r, s), k')
            | BoxedValue v => boxValue (e, s, k) v
            | Var v => (Value (lookup (v, e)), e, s, k)
            | Select (i, m) => (m, e, s, SEL (i, e, k))
            | Unbox (m) => (m, e, s, UNBX (e, k))
            | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
            | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
            | RegionElim (f, r1, r2) => (Var f, e, s, ELIM (r1, r2, e, k))
            | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
            | App (m1, m2) => (m1, e, s, AR (m2, e, k))
            | PrimApp (opr, m1, m2) => (m1, e, s, PR1 (opr, m2, e, k))
            )
        | ELIM (r1, r2, e', k') => 
            (case c of 
              Value (IntLit i) => raise Fail "irrelevant continuation"
            | Value (BoolLit b) => raise Fail "irrelevant continuation"
            | Value (UnitLit) => raise Fail "irrelevant continuation"
            | Value (BarePointer (r, p)) => 
                (case List.find (fn (x, _) => x = r) s of
                  SOME (rn, mv) => 
                    (case List.nth (mv, p) of
                      HeapIntLit i => raise Fail "cannot elim boxint"
                    | HeapBoolLit b => raise Fail "cannot elim boxbool"
                    | HeapUnitLit => raise Fail "cannot elim boxunit"
                    | HeapLambda (x, m, argt) => raise Fail "cannot elim boxlambda"
                    | HeapRegionLambda (r3, a) => 
                        (case a of 
                          Lambda (x, m, argt, r4) => 
                            (BoxedValue (BoxAbs (Lambda (x, substRegVar (r3, r1) m, argt, r2))), e', s, k')
                        | RegionLambda (r4, m, r5) =>
                            (BoxedValue (BoxAbs (RegionLambda (r4, substRegVarAbs (r3, r1) m, r2))), e', s, k')
                        )
                    | HeapTuple (m) => raise Fail "cannot elim boxtuple"
                    | HeapBarePointer (r, p) => raise Fail "cannot elim boxabs"
                    )
                | NONE => raise Fail "unknown region"
                )
            | BoxedValue v => boxValue (e, s, k) v
            | Var v => (Value (lookup (v, e)), e, s, k)
            | Select (i, m) => (m, e, s, SEL (i, e, k))
            | Unbox (m) => (m, e, s, UNBX (e, k))
            | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
            | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
            | RegionElim (f, r1, r2) => (Var f, e, s, ELIM (r1, r2, e, k))
            | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
            | App (m1, m2) => (m1, e, s, AR (m2, e, k))
            | PrimApp (opr, m1, m2) => (m1, e, s, PR1 (opr, m2, e, k))
            )
        )
        (*
            (case c of 
              Value (IntLit i) => 
            | Value (BoolLit b) => 
            | Value (UnitLit) => 
            | Value (BarePointer (r, p)) => 
            | BoxedValue v => 
                (case v of 
                  BoxIntLit (i, r) => 
                | BoxBoolLit (b, r) => 
                | BoxUnitLit r => 
                | BoxAbs a => 
                | BoxTuple ([], r) => raise Fail "not possible"
                | BoxTuple (m::ms, r) => 
                | BoxBarePointer (r1, p, r2) => 
                )
            | Var v => 
            | Select (i, m) => 
            | Unbox (m) => 
            | Let (x, m1, m2, argt) => 
            | LetRegion (r, m) => 
            | RegionElim (f, r1, r2) => 
            | IfElse (m1, m2, m3) => 
            | App (m1, m2) => 
            | PrimApp (opr, m1, m2) => 
            )
          *)
    end

  fun runToCompletion (c : term, e : environment, s : store, k : continuation) : state = 
    if isValue c then
      (case k of
        Empty => (c, e, s, k)
      | _ => runToCompletion (step (c, e, s, k)))
    else runToCompletion (step (c, e, s, k))
end

