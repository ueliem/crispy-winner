signature ERR = sig
  type err
  type pos
  type elem
end

signature PARSER = sig
  structure S : STREAM
  structure E : ERR
  type s = S.stream
  type e = E.err
  include MONADZEROPLUS
  val getstate : s monad
  val putstate : s -> unit monad
  val throw : e -> 'a monad
  val run : 'a monad -> s -> ('a option, e) either * s
  val position : S.pos monad
  val next : S.elem monad
  val many : 'a monad -> 'a list monad
  val many1 : 'a monad -> 'a list monad
  val optional : 'a monad -> 'a option monad
  val eoi : unit monad
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
  val position = getstate >>= (fn st => return (S.position st))
  val next =
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
  val eoi =
    (next >>= (fn _ => zero ()))
    ++ (return ())
  val run = MM.run
end

