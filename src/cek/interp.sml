structure Interp : sig
  datatype environment = 
    EmptyEnv
  | Env of Lang.var * machinevalue * environment

  and machinevalue = 
    MachineInt of int
  | MachineBool of bool
  | MachineUnit
  | MachineTuple of Lang.term * Lang.term
  | MachineClosure of Lang.var * Lang.term * Lang.ty * environment

  type pointername = int
  type regionname = string
  type region = machinevalue list
  type store = (regionname * region) list

  datatype continuation =
    Empty
  | AR of Lang.term * environment * continuation
  | PR of Lang.operator * environment * continuation
  | CALL of Lang.var * Lang.term * environment * continuation
  | LT of Lang.var * Lang.ty * Lang.term * environment * continuation
  | IF of Lang.term * Lang.term * environment * continuation
  | TUP1 of Lang.term * environment * continuation
  | TUP2 of Lang.term * environment * continuation
  | FST of environment * continuation
  | SND of environment * continuation
  | BX of regionname * environment * continuation
  | UNBX of environment * continuation
  | FREERGN of regionname * environment * continuation

  type state = Lang.term * environment * store * continuation

  val lookup : Lang.var * environment -> machinevalue
  val step : state -> state
  val runToCompletion : state -> state
end
=
struct
  open Lang

  datatype environment = 
    EmptyEnv
  | Env of var * machinevalue * environment

  and machinevalue = 
    MachineInt of int
  | MachineBool of bool
  | MachineUnit
  | MachineTuple of term * term
  | MachineClosure of var * term * ty * environment

  type pointername = int
  type regionname = string
  type region = machinevalue list
  type store = (regionname * region) list

  datatype continuation =
    Empty
  | AR of term * environment * continuation
  | PR of operator * environment * continuation
  | CALL of var * term * environment * continuation
  | LT of var * ty * term * environment * continuation
  | IF of term * term * environment * continuation
  | TUP1 of term * environment * continuation
  | TUP2 of term * environment * continuation
  | FST of environment * continuation
  | SND of environment * continuation
  | BX of regionname * environment * continuation
  | UNBX of environment * continuation
  | FREERGN of regionname * environment * continuation

  type state = term * environment * store * continuation

  fun lookup (v : var, EmptyEnv) = raise Fail "var not in env"
  | lookup (v, Env (v', mv, e)) =
      if v = v' then mv
      else lookup (v, e)

  fun removeRegion (r, []) = []
  | removeRegion (r, (rn, reg)::s) =
      if r = rn then s
      else (rn, reg)::(removeRegion (r, s))

  fun step (c : term, e : environment, s : store, k : continuation) : state = 
    let 
      fun valueToMValue (Lang.IntLit i) = MachineInt i
      | valueToMValue (Lang.BoolLit b) = MachineBool b
      | valueToMValue (Lang.UnitLit) = MachineUnit
      | valueToMValue (Lang.Lambda (x, m, t)) = MachineClosure (x, m, t, e)
      | valueToMValue (Lang.Tuple (t1, t2)) = MachineTuple (t1, t2)

      fun putStore (r : regionname, v : Lang.value, s : store) : (regionvar * pointername) * store = 
        case List.partition (fn (x, _) => x = r) s of
          ([], s') => ((r, 0), (r, [valueToMValue v])::s')
        | ([(rn, reg)], s') => ((r, List.length reg), (r, reg @ [valueToMValue v])::s')
        | _ => raise Fail "duplicate region name"
    in
      (case c of
        Value (IntLit i) =>
          (case k of
            Empty => (c, e, s, k)
          | AR (m', e', k') => raise Fail "irrelevant continuation"
          | PR (opr, e', k') => raise Fail "irrelevant continuation"
          | CALL (x', m', e', k') => (m', Env (x', MachineInt i, e'), s, k')
          | LT (x', argt', m', e', k') => (m', Env (x', MachineInt i, e'), s, k')
          | IF (m1, m2, e', k') => raise Fail "irrelevant continuation"
          | TUP1 (m', e', k') => (m', e', s, TUP2 (c, e', k'))
          | TUP2 (m', e', k') => (Value (Tuple (m', c)), e', s, k')
          | FST (e', k') => raise Fail "irrelevant continuation"
          | SND (e', k') => raise Fail "irrelevant continuation"
          | BX (r, e', k') =>
              let val (p, s') = putStore (r, IntLit i, s)
              in
                (Lang.BarePointer p, e', s', k')
              end
          | UNBX (e', k') => raise Fail "irrelevant continuation"
          | FREERGN (r, e', k') => (c, e', removeRegion (r, s), k')
          )
      | Value (BoolLit b) =>
          (case k of
            Empty => (c, e, s, k)
          | AR (m', e', k') => raise Fail "irrelevant continuation"
          | PR (opr, e', k') => raise Fail "irrelevant continuation"
          | CALL (x', m', e', k') => (m', Env (x', MachineBool b, e'), s, k')
          | LT (x', argt', m', e', k') => (m', Env (x', MachineBool b, e'), s, k')
          | IF (m1, m2, e', k') => 
              if b then (m1, e', s, k')
              else (m2, e', s, k')
          | TUP1 (m', e', k') => (m', e', s, TUP2 (c, e', k'))
          | TUP2 (m', e', k') => (Value (Tuple (m', c)), e', s, k')
          | FST (e', k') => raise Fail "irrelevant continuation"
          | SND (e', k') => raise Fail "irrelevant continuation"
          | BX (r, e', k') =>
              let val (p, s') = putStore (r, BoolLit b, s)
              in
                (Lang.BarePointer p, e', s', k')
              end
          | UNBX (e', k') => raise Fail "irrelevant continuation"
          | FREERGN (r, e', k') => (c, e', removeRegion (r, s), k')
          )
      | Value (UnitLit) =>
          (case k of
            Empty => (c, e, s, k)
          | AR (m', e', k') => raise Fail "irrelevant continuation"
          | PR (opr, e', k') => raise Fail "irrelevant continuation"
          | CALL (x', m', e', k') => (m', Env (x', MachineUnit, e'), s, k')
          | LT (x', argt', m', e', k') => (m', Env (x', MachineUnit, e'), s, k')
          | IF (m1, m2, e', k') => raise Fail "irrelevant continuation"
          | TUP1 (m', e', k') => (m', e', s, TUP2 (c, e', k'))
          | TUP2 (m', e', k') => (Value (Tuple (m', c)), e', s, k')
          | FST (e', k') => raise Fail "irrelevant continuation"
          | SND (e', k') => raise Fail "irrelevant continuation"
          | BX (r, e', k') =>
              let val (p, s') = putStore (r, UnitLit, s)
              in
                (Lang.BarePointer p, e', s', k')
              end
          | UNBX (e', k') => raise Fail "irrelevant continuation"
          | FREERGN (r, e', k') => (c, e', removeRegion (r, s), k')
          )
      | Value (Lambda (x, m, argt)) => 
          (case k of
            Empty => (c, e, s, k)
          | AR (m', e', k') => (m', e', s, CALL (x, m, e, k'))
          | PR (opr, e', k') => raise Fail "irrelevant continuation"
          | CALL (x', m', e', k') => (m', Env (x', MachineClosure (x, m, argt, e), e'), s, k')
          | LT (x', argt', m', e', k') => (m', Env (x', MachineClosure (x, m, argt, e), e'), s, k')
          | IF (m1, m2, e', k') => raise Fail "irrelevant continuation"
          | TUP1 (m', e', k') => (m', e', s, TUP2 (c, e', k'))
          | TUP2 (m', e', k') => (Value (Tuple (m', c)), e', s, k')
          | FST (e', k') => raise Fail "irrelevant continuation"
          | SND (e', k') => raise Fail "irrelevant continuation"
          | BX (r, e', k') =>
              let val (p, s') = putStore (r, Lambda (x, m, argt), s)
              in
                (Lang.BarePointer p, e', s', k')
              end
          | UNBX (e', k') => raise Fail "irrelevant continuation"
          | FREERGN (r, e', k') => (c, e', removeRegion (r, s), k')
          )
      | Value (Tuple (m1, m2)) =>
          if (isValue m1) andalso (isValue m2) then
            (case k of
              Empty => (c, e, s, k)
            | AR (m', e', k') => raise Fail "irrelevant continuation"
            | PR (opr, e', k') =>
                (case (m1, m2) of
                  (Value (IntLit i1), Value (IntLit i2)) =>
                    (case opr of
                      "+" => (Value (IntLit (i1 + i2)), e', s, k')
                    | "-" => (Value (IntLit (i1 - i2)), e', s, k')
                    | "*" => (Value (IntLit (i1 * i2)), e', s, k')
                    | "<" => (Value (BoolLit (i1 < i2)), e', s, k')
                    | "=" => (Value (BoolLit (i1 = i2)), e', s, k')
                    | _ => raise Fail "undefined operator"
                    )
                | _ => raise Fail "cannot do prim op on these types"
                )
            | CALL (x', m', e', k') => (m', Env (x', MachineTuple (m1, m2), e'), s, k')
            | LT (x', argt', m', e', k') => (m', Env (x', MachineTuple (m1, m2), e'), s, k')
            | IF (m1, m2, e', k') => raise Fail "irrelevant continuation"
            | TUP1 (m', e', k') => (m', e', s, TUP2 (c, e', k'))
            | TUP2 (m', e', k') => (Value (Tuple (m', c)), e', s, k')
            | FST (e', k') => (m1, e', s, k')
            | SND (e', k') => (m2, e', s, k')
            | BX (r, e', k') =>
                let val (p, s') = putStore (r, Tuple (m1, m2), s)
                in
                  (Lang.BarePointer p, e', s', k')
                end
            | UNBX (e', k') => raise Fail "irrelevant continuation"
            | FREERGN (r, e', k') => (c, e', removeRegion (r, s), k')
            )
          else (m1, e, s, TUP1 (m2, e, k))
      | BoxedValue (v, r) => (Value v, e, s, BX (r, e, k))
      | BarePointer (r, p) =>
          (case k of
            Empty => raise Fail "irrelevant continuation"
          | AR (m', e', k') => raise Fail "irrelevant continuation"
          | PR (opr, e', k') => raise Fail "irrelevant continuation"
          | CALL (x', m', e', k') => raise Fail "irrelevant continuation"
          | LT (x', argt', m', e', k') => raise Fail "irrelevant continuation"
          | IF (m1, m2, e', k') => raise Fail "irrelevant continuation"
          | TUP1 (m', e', k') => raise Fail "irrelevant continuation"
          | TUP2 (m', e', k') => raise Fail "irrelevant continuation"
          | FST (e', k') => raise Fail "irrelevant continuation"
          | SND (e', k') => raise Fail "irrelevant continuation"
          | BX (r, e', k') => raise Fail "irrelevant continuation"
          | UNBX (e', k') => 
              (case List.find (fn (x, _) => x = r) s of
                SOME (rn, mv) => 
                  (case List.nth (mv, p) of
                    MachineInt i => (Value (IntLit i), e, s, k')
                  | MachineBool b => (Value (BoolLit b), e, s, k')
                  | MachineUnit => (Value (UnitLit), e, s, k')
                  | MachineTuple (m1, m2) => (Value (Tuple (m1, m2)), e, s, k')
                  | MachineClosure (x, m, argt, e') => (Value (Lambda (x, m, argt)), e', s, k')
                  )
              | NONE => raise Fail "unknown region")
          | FREERGN (r, e', k') => (c, e', removeRegion (r, s), k')
          )
      | Var v => 
          (case lookup (v, e) of
            MachineInt i => (Value (IntLit i), e, s, k)
          | MachineBool b => (Value (BoolLit b), e, s, k)
          | MachineUnit => (Value (UnitLit), e, s, k)
          | MachineTuple (m1, m2) => (Value (Tuple (m1, m2)), e, s, k)
          | MachineClosure (x, m, argt, e') => (Value (Lambda (x, m, argt)), e', s, k)
          )
      | First (m) => (m, e, s, FST (e, k))
      | Second (m) => (m, e, s, SND (e, k))
      | Unbox (m) => (m, e, s, UNBX (e, k))
      | Let (x, m1, m2, argt) => (m1, e, s, LT (x, argt, m2, e, k))
      | LetRegion (r, m) => (m, e, s, FREERGN (r, e, k))
      | IfElse (m1, m2, m3) => (m1, e, s, IF (m2, m3, e, k))
      | App (m1, m2) => (m1, e, s, AR (m2, e, k))
      | PrimApp (opr, m) => (m, e, s, PR (opr, e, k))
      )
    end

  fun runToCompletion (c : term, e : environment, s : store, k : continuation) : state = 
    if isValue c then
      (case k of
        Empty => (c, e, s, k)
      | _ => runToCompletion (step (c, e, s, k)))
    else runToCompletion (step (c, e, s, k))
end

