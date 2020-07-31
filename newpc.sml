signature STRM =
sig
  type stream
  type elem
  type pos
  val uncons : stream -> (elem * stream) option
  val peek : stream -> elem option
  val position : stream -> pos
  val equiv : elem * elem -> bool
end

functor StreamFunctor (
  structure S : MONO_VECTOR;
  val eq : S.elem * S.elem -> bool
) : STRM =
struct
  type pos = int
  type stream = { s : S.vector, pos : pos }
  type elem = S.elem

  fun uncons (strm) = 
    let
      val pos = #pos strm
      val len = S.length (#s strm)
    in
      if pos < len then
        SOME (S.sub (#s strm, pos), { s = #s strm, pos = pos + 1 })
      else NONE
    end

  fun peek (strm) =
    let
      val pos = #pos strm
      val len = S.length (#s strm)
    in
      if pos < len then
        SOME (S.sub (#s strm, pos))
      else NONE
    end

  fun position (strm) = #pos strm

  val equiv = eq

end

signature PERROR =
sig
  type err
  type pos
  type elem
  val expected : pos -> elem -> err
  val unexpected : pos -> elem -> err
  val message : pos -> string -> err
  val empty : pos -> err
end

functor StreamError (structure S : STRM) :
sig
  include PERROR
  datatype e =
    Expected of elem
  | Unexpected of elem
  | Message of string
  val add : err -> e -> err
end
=
struct
  type elem = S.elem
  datatype e =
    Expected of elem
  | Unexpected of elem
  | Message of string
  type pos = S.pos
  type err = S.pos * e list
  fun expected p t = (p, [Expected t])
  fun unexpected p t = (p, [Unexpected t])
  fun message p m = (p, [Message m])
  fun empty p = (p, [Message ""])
  fun add x y =
    let val (p, l) = x
    in
      (case y of
        Expected z =>
          if List.exists (fn w =>
            (case w of
              Expected v => S.equiv (v, z)
            | _ => false)) l then
              x
          else (p, y::l)
      | Unexpected z =>
          if List.exists (fn w =>
            (case w of
              Unexpected v => S.equiv (v, z)
            | _ => false)) l then
              x
          else (p, y::l)
      | Message _ => (p, y::l))
    end
end

functor ParserT (structure S : STRM; structure E : PERROR; sharing type S.pos = E.pos) : 
sig
  type pst = (S.stream)
  structure PState : MONAD

  datatype 'output ParseResult =
    Ok of 'output
  | Error of E.err
  type 'a Parser = 'a ParseResult PState.monad
  include MONADZEROPLUS where type 'a monad = 'a Parser

  val fail : unit -> 'a monad
  val next : unit -> S.elem monad
  val position : unit -> S.pos monad
  val many : 'a Parser -> 'a list Parser
  val many1 : 'a Parser -> 'a list Parser
  val optional : 'a Parser -> 'a option Parser
  val lift : 'a PState.monad -> 'a ParseResult PState.monad
end
=
struct
  type pst = (S.stream)
  structure PState = StateFunctor(type s = pst)

  datatype 'output ParseResult =
    Ok of 'output
  | Error of E.err
  type 'a Parser = 'a ParseResult PState.monad
  type 'a monad = 'a Parser

  fun return x = PState.return (Ok x)

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

  fun op ++ (p1 : 'a monad, p2 : 'a monad) : 'a monad =
    ((fn s => case p1 s of
      (Ok r, s') => (Ok r, s')
    | (Error e1, s') =>
        (case p2 s of
          (Ok r, s'') => (Ok r, s'')
        | (Error e2, s'') => (Error e2, s)
        )))

  fun position () =
    lift PState.get >>= (fn (st) =>
      return (S.position st)
    )

  fun fail () = 
    position () >>= (fn p =>
      PState.return (Error (E.empty p))
    )

  fun zero () = fail ()

  fun next () =
    lift PState.get >>= (fn (st) =>
      (case S.uncons st of
        SOME (x, xs) => 
          lift (PState.put (xs)) >>= (fn _ =>
            PState.return (Ok x))
      | NONE => fail ())
    )

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

