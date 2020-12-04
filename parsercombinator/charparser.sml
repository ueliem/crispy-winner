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
  sharing type S.pos = E.pos;
  structure M : MONAD) : sig
  include CHARPARSER
  structure M : MONAD end = struct
  structure CParser =
    ParserT(structure S = S; structure E = E; structure M = M)
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
  include ERR where type elem = char where type pos = int end;
  structure M : MONAD) : sig
  include CHARPARSER
  structure M : MONAD end = struct
  structure CP =
    CharParser (structure S = CharVectorStream; structure E = E; structure M = M)
  open CP
end

functor CharFileParser (structure E : sig
  include ERR where type elem = char where type pos = int * int end;
  structure M : MONAD) : sig
  include CHARPARSER
  structure M : MONAD end = struct
  structure CP =
    CharParser (structure S = CharFileStream; structure E = E; structure M = M)
  open CP
end

