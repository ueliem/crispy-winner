structure TErr = struct
  type err = unit
  type pos = CharFileStream.pos
  type elem = CharFileStream.item
end

signature TOKEN = sig
  eqtype t
  val symbolList : char list
  val makeKeyword : string -> t option
  val makeIdentifier : string -> t
  val makeSymbol : string -> t
  val makeInteger : string -> t option
  val makeLPar : unit -> t
  val makeRPar : unit -> t
  val stringOf : t -> string
end

functor Tokenizer (structure T : TOKEN;
  structure TE : sig include ERR where type elem = char end;
  structure CP : sig
    include CHARPARSER
    structure M : MONAD
  end) : sig
  include CHARPARSER
  structure M : MONAD
  structure TE : sig include ERR where type elem = char end;
  structure T : TOKEN;
  structure CP : CHARPARSER
  type t = T.t
  type tok = CP.S.pos * t
  val whitespace : char list monad
  val keyword : t monad
  val ident : t monad
  val integer : t monad
  val sym : t monad
  val leftpar : t monad
  val rightpar : t monad
  val token : tok monad
  val tokenize : tok list monad
  structure TokenVector : sig
    include MONO_VECTOR
    eqtype item
  end
  structure TokenStream : sig
    include STREAM
    val fromList : item list -> stream
  end
end = struct
  structure T = T
  structure TE = TE
  structure M = CP.M
  structure CP = CP
  open CP
  type t = T.t
  type tok = CP.S.pos * t
  val whitespace = many space
  val keyword =
    many1 letter >>= (fn x =>
      case T.makeKeyword (String.implode x) of
       SOME k => return k | NONE => zero ())
  val ident =
    letter >>= (fn x => many alphanum >>= (fn xs =>
      return (T.makeIdentifier (String.implode (x::xs)))))
  val integer =
    many1 digit >>= (fn x =>
      case T.makeInteger (String.implode x) of
       SOME i => return i | NONE => zero ())
  val sym =
    many1 (symbol) >>= (fn x => return (T.makeSymbol (String.implode x)))
  val leftpar = lpar >>= (fn x => return (T.makeLPar ()))
  val rightpar = rpar >>= (fn x => return (T.makeRPar ()))
  val token =
    position >>= (fn p =>
    (keyword ++ ident ++ sym ++ integer ++ leftpar ++ rightpar) >>= (fn x =>
    whitespace >>= (fn _ => return (p, x))))
  val tokenize =
    (many1 token >>= (fn ts => eoi >>= (fn _ => return ts)))
  structure TokenVector : sig
    include MONO_VECTOR
    eqtype item
  end = struct
    open Vector
    type vector = tok vector
    type elem = tok
    type item = tok
  end
  structure TokenStream : sig
    include STREAM
    val fromList : item list -> stream
  end = struct
    structure TS = MonoVectorStream (structure S = TokenVector;
      val eq = (fn (x, y) => x = y);
      val stringOfPos = (fn p => Int.toString p);
      val stringOfElem = (fn (p, t) => T.stringOf t))
    open TS
    fun fromList l = { s = (TokenVector.fromList l), pos = 0 }
  end
end

