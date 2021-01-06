signature CHARPARSER = sig
  include PARSER
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
  include STREAM where type item = char end;
  type e; structure Base : MONAD) : sig
  include CHARPARSER end = struct
  structure CParser =
    ParserT(structure S = S; type e = e; structure Base = Base)
  open CParser

  val symbols = [#"+", #"-", #"*", #"/",
                 #"/", #"=", #">", #"<",
                 #":", #";", #".", #"|",
                 #"_"]
  val lpar = satisfies (fn x => x = #"(")
  val rpar = satisfies (fn x => x = #")")
  val symbol = satisfies (fn x => List.exists (fn y => x = y) symbols)
  val comma = satisfies (fn x => x = #",")
  val digit = satisfies Char.isDigit
  val letter = satisfies Char.isAlpha
  val alphanum = satisfies Char.isAlphaNum
  val space = satisfies Char.isSpace
end

functor CharVectorParser (type e; structure Base : MONAD) : sig
  include CHARPARSER end = struct
  structure CP =
    CharParser (structure S = CharVectorStream;
      type e = e; structure Base = Base)
  open CP
end

functor CharFileParser (type e; structure Base : MONAD) : sig
  include CHARPARSER end = struct
  structure CP =
    CharParser (structure S = CharFileStream;
      type e = e; structure Base = Base)
  open CP
end

