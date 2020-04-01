functor PT (structure S : STRM) : MONADPLUSZERO = 
struct
  structure P = OptionT (structure M = StateFunctor (type s = ((int * int) * S.stream)))
  open P
end


functor ParserT (structure S : STRM) : 
sig
  type pst = ((int * int) * S.stream)
  structure PState : MONAD

  datatype 'output ParseResult =
    Ok of 'output
  | Error of int
  type 'a Parser = 'a ParseResult PState.monad
  include MONADPLUSZERO where type 'a monad = 'a Parser

  val fail : unit -> 'a monad
  val next : unit -> S.elem monad
  val runParser : 'a monad -> pst -> ('a * pst)
  val advanceFPosCol : int -> unit Parser
  val advanceFPosLine : int -> unit Parser
  val many : 'a Parser -> 'a list Parser
  val many1 : 'a Parser -> 'a list Parser
  val optional : 'a Parser -> 'a option Parser
  val lift : 'a PState.monad -> 'a ParseResult PState.monad
end
=
struct
  type pst = ((int * int) * S.stream)
  structure PState = StateFunctor(type s = pst)

  datatype 'output ParseResult =
    Ok of 'output
  | Error of int
  type 'a Parser = 'a ParseResult PState.monad
  type 'a monad = 'a Parser

  fun return x = PState.return (Ok x)

  fun fail () = PState.return (Error 0)

  fun op >>= (m : 'a ParseResult PState.monad, f : 'a -> 'b ParseResult PState.monad) : 'b ParseResult PState.monad = 
    PState.>>= (m, (fn (x : 'a ParseResult) =>
      case x of
        Ok y => f y
      | Error e => PState.return (Error e)
    ))

  fun lift (m : 'a PState.monad) : 'a ParseResult PState.monad =
    PState.>>= (m, fn (x : 'a) =>
      PState.return (Ok x)
    )

  val zero = PState.State (fn s => (Error 0, s))

  fun op ++ (p1 : 'a monad, p2 : 'a monad) : 'a monad =
    (PState.State (fn s => case PState.runState p1 s of
      (Ok r, s') => (Ok r, s')
    | (Error e1, s') =>
        (case PState.runState p2 s of
          (Ok r, s'') => (Ok r, s'')
        | (Error e2, s'') => (Error e2, s)
        )))

  fun next () =
    lift PState.get >>= (fn (fpos, st) =>
      (case S.uncons st of
        SOME (x, xs) => 
          lift (PState.put (fpos, xs)) >>= (fn _ =>
            PState.return (Ok x))
      | NONE => PState.return (Error 0))
    )

  fun runParser p = (PState.runState p)

  fun advanceFPosCol i =
    lift PState.get >>= (fn ((l, c), st) =>
    lift (PState.put ((l, c + i), st)))

  fun advanceFPosLine i =
    lift PState.get >>= (fn ((l, c), st) =>
    lift (PState.put ((l + i, c), st)))

  fun setFPos p = 
    lift PState.get >>= (fn (_, st) =>
    lift (PState.put (p, st)))

  fun many (p : 'a Parser) : 'a list Parser =
    p >>= (fn x =>
    many p >>= (fn y =>
      return (x::y)
    ))
    ++ (return [])

  fun many1 (p : 'a Parser) : 'a list Parser =
    p >>= (fn x =>
    many p >>= (fn y =>
      return (x::y)
    ))

  fun optional (p : 'a Parser) : 'a option Parser =
    p >>= (fn x =>
      return (SOME x)
    )
    ++ (return NONE)

end

