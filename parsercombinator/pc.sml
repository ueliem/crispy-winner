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
end

signature CHARPARSER = sig
  include PARSER
  val satisfies : (char -> bool) -> char monad
  val lpar : char monad
  val rpar : char monad
  val comma : char monad
  val symbol : char monad
  val digit : char monad
  val letter : char monad
  val alphanum : char monad
  val space : char monad
end

functor CharParser (structure S : sig
  include STREAM where type elem = char end;
  structure E : sig include ERR where type elem = char end;
  sharing type S.pos = E.pos) : sig
  include CHARPARSER
end = struct
  structure CParser = ParserT(structure S = S; structure E = E)
  open CParser

  val symbols = [#"+", #"-", #"*", #"/",
                 #"/", #"=", #">", #"<",
                 #":", #";", #".", #"|",
                 #"_"]
  fun satisfies f = 
    next >>= (fn x =>
    if f x then return x else zero ())
  val lpar = satisfies (fn x => x = #"(")
  val rpar = satisfies (fn x => x = #")")
  val symbol = satisfies (fn x => List.exists (fn y => x = y) symbols)
  val comma = satisfies (fn x => x = #",")
  val digit = satisfies Char.isAlphaNum
  val letter = satisfies Char.isAlpha
  val alphanum = satisfies Char.isAlphaNum
  val space = satisfies Char.isSpace
end

functor CharVectorParser (structure E : sig
  include ERR where type elem = char where type pos = int end) : CHARPARSER =
struct
  structure CP = CharParser (structure S = CharVectorStream; structure E = E)
  open CP
end

functor CharFileParser (structure E : sig
  include ERR where type elem = char where type pos = int * int end) : CHARPARSER =
struct
  structure CP = CharParser (structure S = CharFileStream; structure E = E)
  open CP
end

