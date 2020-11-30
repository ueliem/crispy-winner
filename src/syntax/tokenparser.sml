structure PErr = struct
  type err = unit
  type pos = TokenStream.pos
  type elem = TokenStream.elem
end

structure TokenParser : sig
  include PARSER
  val intLit : int monad
  val boolLit : bool monad
  val lpar : unit monad
  val rpar : unit monad
  val symbol : string monad
  val period : unit monad
  val colon : unit monad
  val semicolon : unit monad
  val pipe : unit monad
  val defined : unit monad
  val rightarrow : unit monad
  val underscore : unit monad
  val ident : string monad
  val kwFuncT : unit monad
  val kwSig : unit monad
  val kwFunctor : unit monad
  val kwStruct : unit monad
  val kwTransparent : unit monad
  val kwSet : unit monad
  val kwType : unit monad
  val kwComp : unit monad
  val kwTrans : unit monad
  val kwForAll : unit monad
  val kwFun : unit monad
  val kwCase : unit monad
  val kwOf : unit monad
  val kwIf : unit monad
  val kwThen : unit monad
  val kwElse : unit monad
  val kwLet : unit monad
  val kwIn : unit monad
  val kwEnd : unit monad
  val kwInt : unit monad
  val kwBool : unit monad
  val kwInductive : unit monad
  val tokenEOI : unit monad
end = struct
  structure TP = ParserT (
    structure S = TokenStream;
    structure E = PErr)
  open TP

  val intLit = next >>= (fn (p, x) =>
    case x of Tokenizer.Integer i => return i | _ => zero ())
  val boolLit = next >>= (fn (p, x) =>
    case x of Tokenizer.Boolean b => return b | _ => zero ())
  val lpar = next >>= (fn (p, x) =>
    case x of Tokenizer.LPar => return () | _ => zero ())
  val rpar = next >>= (fn (p, x) =>
    case x of Tokenizer.LPar => return () | _ => zero ())
  val symbol = next >>= (fn (p, x) =>
    case x of Tokenizer.Symbol s => return s
    | _ => zero ())
  val matchSymbol =
    (fn s => symbol >>= (fn s' =>
    if s = s' then return () else zero ()))
  val period = matchSymbol "."
  val colon = matchSymbol ":"
  val semicolon = matchSymbol ";"
  val pipe = matchSymbol "|"
  val defined = matchSymbol ":="
  val rightarrow = matchSymbol "=>"
  val underscore = matchSymbol "_"
  val ident = next >>= (fn (p, x) =>
    case x of Tokenizer.Identifier s => return s
    | _ => zero ())
  val kwFuncT = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwSig = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwFunctor = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwStruct = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwTransparent = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwSet = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwType = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwComp = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwTrans = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwForAll = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwFun = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwCase = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwOf = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwIf = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwThen = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwElse = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwLet = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwIn = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwEnd = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwInt = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwBool = next >>= (fn (p, x) =>
    case x of Tokenizer.KWFuncT => return () | _ => zero ())
  val kwInductive = next >>= (fn (p, x) =>
    case x of Tokenizer.KWInductive => return () | _ => zero ())
  val tokenEOI = next >>= (fn (p, x) =>
    case x of Tokenizer.EOI => return () | _ => zero ())
end

structure TokenParserUtil = MUtil (structure M = TokenParser)

