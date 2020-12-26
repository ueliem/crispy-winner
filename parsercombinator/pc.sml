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
  structure M : MONAD
  structure PST : STATET
  structure PEXC : EXCEPTIONT
  structure POPT : OPTIONT
  include MONADZEROPLUS
  val lift : 'a M.monad -> 'a monad
  val getstate : s monad
  val putstate : s -> unit monad
  val throw : e -> 'a monad
  val position : S.pos monad
  val next : S.item monad
  val many : 'a monad -> 'a list monad
  val many1 : 'a monad -> 'a list monad
  val optional : 'a monad -> 'a option monad
  val eoi : unit monad
end

functor ParserT (structure S : STREAM;
  structure E : ERR;
  sharing type S.pos = E.pos;
  sharing type S.item = E.elem;
  structure M : MONAD) : sig
    include PARSER end = struct
  structure S = S
  structure E = E
  structure M = M
  type s = S.stream
  type e = E.err
  structure PST = StateT (type s = s; structure M = M)
  structure PEXC = ExceptionT (type e = e; structure M = PST)
  structure POPT = OptionT (structure M = PEXC)
  open POPT

  val getstate = lift (PEXC.lift PST.get)
  val putstate = (fn st => lift (PEXC.lift (PST.put st)))
  fun throw r = PEXC.throw r
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
end

