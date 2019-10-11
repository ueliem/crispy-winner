type var = string

type operator = string

datatype term = 
  IntLit of int 
| Var of var
| Lambda of var * term
| Tuple of term * term
| First of term
| Second of term
| Let of var * term * term
| IfZero of term * term * term
| App of term * term
| PrimApp of operator * term

datatype environment = 
  EmptyEnv
| Env of var * machinevalue * environment

and machinevalue = 
  MachineInt of int
| MachineTuple of term * term
| MachineClosure of var * term * environment

datatype continuation =
  Empty
| AR of term * environment * continuation
| PR of operator * environment * continuation
| CALL of var * term * environment * continuation
| LT of var * term * environment * continuation
| IF of term * term * environment * continuation
| TUP1 of term * environment * continuation
| TUP2 of term * environment * continuation
| FST of environment * continuation
| SND of environment * continuation

type state = term * environment * continuation

fun lookup (v : var, EmptyEnv) = raise Fail "var not in env"
| lookup (v, Env (v', mv, e)) =
    if v = v' then mv
    else lookup (v, e)

fun isValue (IntLit _) = true
| isValue (Var _) = false
| isValue (Lambda _) = true
| isValue (Tuple (m1, m2)) = (isValue m1) andalso (isValue m2)
| isValue (First _) = false
| isValue (Second _) = false
| isValue (Let _) = false
| isValue (IfZero _) = false
| isValue (App _) = false
| isValue (PrimApp _) = false

fun step (c : term, e : environment, k : continuation) : state = 
  (case c of
    IntLit i =>
      (case k of
        Empty => (c, e, k)
      | AR (m', e', k') => raise Fail "irrelevant continuation"
      | PR (opr, e', k') => raise Fail "irrelevant continuation"
      | CALL (x', m', e', k') => (m', Env (x', MachineInt i, e'), k')
      | LT (x', m', e', k') => (m', Env (x', MachineInt i, e'), k')
      | IF (m1, m2, e', k') => 
          if i = 0 then (m1, e', k')
          else (m2, e', k')
      | TUP1 (m', e', k') => (m', e', TUP2 (c, e', k'))
      | TUP2 (m', e', k') => (Tuple (m', c), e', k')
      | FST (e', k') => raise Fail "irrelevant continuation"
      | SND (e', k') => raise Fail "irrelevant continuation"
      )
  | Var v => 
      (case lookup (v, e) of
        MachineInt i => (IntLit i, e, k)
      | MachineTuple (m1, m2) => (Tuple (m1, m2), e, k)
      | MachineClosure (x, m, e') => (Lambda (x, m), e', k)
      )
  | Lambda (x, m) => 
      (case k of
        Empty => (c, e, k)
      | AR (m', e', k') => (m', e', CALL (x, m, e, k'))
      | PR (opr, e', k') => raise Fail "irrelevant continuation"
      | CALL (x', m', e', k') => (m', Env (x', MachineClosure (x, m, e), e'), k')
      | LT (x', m', e', k') => (m', Env (x', MachineClosure (x, m, e), e'), k')
      | IF (m1, m2, e', k') => raise Fail "irrelevant continuation"
      | TUP1 (m', e', k') => (m', e', TUP2 (c, e', k'))
      | TUP2 (m', e', k') => (Tuple (m', c), e', k')
      | FST (e', k') => raise Fail "irrelevant continuation"
      | SND (e', k') => raise Fail "irrelevant continuation"
      )
  | First (m) => (m, e, FST (e, k))
  | Second (m) => (m, e, SND (e, k))
  | Tuple (m1, m2) =>
      if (isValue m1) andalso (isValue m2) then
        (case k of
          Empty => (c, e, k)
        | AR (m', e', k') => raise Fail "irrelevant continuation"
        | PR (opr, e', k') =>
            (case (m1, m2) of
              (IntLit i1, IntLit i2) =>
                (case opr of
                  "+" => (IntLit (i1 + i2), e', k')
                | "-" => (IntLit (i1 - i2), e', k')
                | "*" => (IntLit (i1 * i2), e', k')
                | _ => raise Fail "undefined operator"
                )
            | _ => raise Fail "cannot do prim op on these types"
            )
        | CALL (x', m', e', k') => (m', Env (x', MachineTuple (m1, m2), e'), k')
        | LT (x', m', e', k') => (m', Env (x', MachineTuple (m1, m2), e'), k')
        | IF (m1, m2, e', k') => raise Fail "irrelevant continuation"
        | TUP1 (m', e', k') => (m', e', TUP2 (c, e', k'))
        | TUP2 (m', e', k') => (Tuple (m', c), e', k')
        | FST (e', k') => (m1, e', k')
        | SND (e', k') => (m2, e', k')
        )
      else (m1, e, TUP1 (m2, e, k))
  | Let (x, m1, m2) => (m1, e, LT (x, m2, e, k))
  | IfZero (m1, m2, m3) => (m1, e, IF (m2, m3, e, k))
  | App (m1, m2) => (m1, e, AR (m2, e, k))
  | PrimApp (opr, m) => (m, e, PR (opr, e, k))
  )

fun runToCompletion (c : term, e : environment, k : continuation) : state = 
  if isValue c then
    (case k of
      Empty => (c, e, k)
    | _ => runToCompletion (step (c, e, k)))
  else runToCompletion (step (c, e, k))

val prog = App (Lambda ("x", Var "x"), IntLit 7)

fun main () =
let
  val _ = PolyML.print_depth 100
  val _ = PolyML.print prog
  val initstate = (prog, EmptyEnv, Empty)
  val _ = PolyML.print initstate
  val _ = PolyML.print (runToCompletion initstate)
in
  ()
end

