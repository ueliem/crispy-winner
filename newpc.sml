exception PExc

signature STRM =
sig
  type stream
  type elem
  type pos
  val uncons : stream -> (elem * stream) option
  val peek : stream -> elem option
  val position : stream -> pos
  val equiv : elem * elem -> bool
  val pcompare : pos * pos -> int
  val elem_to_string : elem -> string
  val pos_to_string : pos -> string
end

functor StreamFunctor (
  structure S : MONO_VECTOR;
  val eq : S.elem * S.elem -> bool;
  val estr : S.elem -> string
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

  fun pcompare (p1, p2) =
    if p1 < p2 then ~1
    else if p1 = p2 then 0
    else 1

  val elem_to_string = estr

  val pos_to_string = Int.toString

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
  val errpos : err -> pos
  val merge : err -> err -> err
  val tostring : err -> string
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
  fun errpos (p, el) = p
  fun merge (p1, el1) (p2, el2) =
    (p1, el1 @ el2)
  fun tostring (p, el) =
    String.concatWith " " ((map (fn r => 
      (case r of
        Expected x => String.concat ["expected ", S.elem_to_string x]
      | Unexpected x => String.concat ["unexpected ", S.elem_to_string x]
      | Message m => m)
    ) el) @ ["on", S.pos_to_string p])
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

functor ParserT (structure S : STRM;
  structure E : PERROR;
  sharing type S.pos = E.pos;
  sharing type S.elem = E.elem) : 
sig
  type pst = (S.stream)
  structure PState : MONAD

  datatype 'output ParseResult =
    Ok of 'output
  | Error of E.err
  type 'a Parser = 'a ParseResult PState.monad
  include MONADZEROPLUS where type 'a monad = 'a Parser

  val fail : unit -> 'a monad
  val expected : S.elem -> 'a monad
  val unexpected : S.elem -> 'a monad
  val message : string -> 'a monad
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

  fun choose (e1, s1) (e2, s2) =
    (case S.pcompare (E.errpos e1, E.errpos e2) of
      ~1 => (Error e2, s2)
    | 0 => (Error (E.merge e1 e2), s2)
    | 1 => (Error e1, s1)
    | _ => raise PExc
    )

  fun op ++ (p1 : 'a monad, p2 : 'a monad) : 'a monad =
    ((fn s => case p1 s of
      (Ok r, s') => (Ok r, s')
    | (Error e1, s') =>
        (case p2 s of
          (Ok r, s'') => (Ok r, s'')
        | (Error e2, s'') => (*(Error e2, s'')*) choose (e1, s') (e2, s'')
        )))

  fun position () =
    lift PState.get >>= (fn (st) =>
      return (S.position st)
    )

  fun fail () = 
    position () >>= (fn p =>
      PState.return (Error (E.empty p))
    )

  fun expected t =
    position () >>= (fn p =>
      PState.return (Error (E.expected p t)))
  fun unexpected t =
    position () >>= (fn p =>
      PState.return (Error (E.unexpected p t)))
  fun message m =
    position () >>= (fn p =>
      PState.return (Error (E.message p m)))

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

