signature ERR = sig
  type err
  type pos
  type elem
end

signature PARSER = sig
  structure S : STREAM
  structure E : ERR
  type s = S.stream
  include MONADZEROPLUS
  val getstate : s monad
  val putstate : s -> unit monad
  val throw : E.err -> 'a monad
  val position : unit -> S.pos monad
  val next : unit -> S.elem monad
  val many : 'a monad -> 'a list monad
  val many1 : 'a monad -> 'a list monad
  val optional : 'a monad -> 'a option monad
end

functor ParserT (structure S : STREAM;
  structure E : ERR;
  sharing type S.pos = E.pos;
  sharing type S.elem = E.elem) : PARSER =
struct
  structure S = S
  structure E = E
  type s = S.stream
  type e = E.err
  structure M = StateFunctor (type s = s)
  structure MM = ExceptionT (type e = e; structure M = M)
  structure MMM = OptionT (structure M = MM)
  open MMM

  val getstate = lift (MM.lift M.get)
  val putstate = (fn st => lift (MM.lift (M.put st)))
  fun throw r = MM.throw r
  fun position () = getstate >>= (fn st => return (S.position st))
  fun next () =
    getstate >>= (fn st =>
      (case S.uncons st of
        SOME (x, xs) => 
          lift (putstate xs) >>= (fn _ => return x)
      | NONE => zero ()))
  fun many p =
    p >>= (fn x => many p >>= (fn y => return (x::y)))
    ++ (return [])
  fun many1 p =
    p >>= (fn x =>
    many p >>= (fn y => return (x::y)))
  fun optional p =
    p >>= (fn x => return (SOME x))
    ++ (return NONE)
end

functor CharParser (structure S : sig
  include STREAM where type elem = char end;
  structure E : sig include ERR where type elem = char end;
  sharing type S.pos = E.pos) : sig
  include PARSER
  val satisfies : (char -> bool) -> char monad
  val lpar : unit -> char monad
  val rpar : unit -> char monad
  val lcurly : unit -> char monad
  val rcurly : unit -> char monad
  val comma : unit -> char monad
  val symbol : unit -> char monad
  val digit : unit -> char monad
  val letter : unit -> char monad
  val alphanum : unit -> char monad
  val space : unit -> char monad
end = struct
  structure CParser = ParserT(structure S = S; structure E = E)
  open CParser

  val symbols = [#"+", #"-", #"*", #"/", #"=", #">", #"<", #":"]
  fun satisfies f = 
    next () >>= (fn x =>
    if f x then return x else zero ())
  fun lpar () = satisfies (fn x => x = #"(")
  fun rpar () = satisfies (fn x => x = #")")
  fun lcurly () = satisfies (fn x => x = #"{")
  fun rcurly () = satisfies (fn x => x = #"}")
  fun symbol () = satisfies (fn x => List.exists (fn y => x = y) symbols)
  fun comma () = satisfies (fn x => x = #",")
  fun digit () = satisfies Char.isAlphaNum
  fun letter () = satisfies Char.isAlpha
  fun alphanum () = satisfies Char.isAlphaNum
  fun space () = satisfies Char.isSpace
end

