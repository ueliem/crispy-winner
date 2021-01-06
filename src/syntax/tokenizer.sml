structure MTSTokenizer : sig
  include CHARPARSER
  type t = MTSToken.t
  type tok = TokenStream.item
  val whitespace : char list monad
  val ident : t monad
  val integer : t monad
  val sym : t monad
  val leftpar : t monad
  val rightpar : t monad
  val token : tok monad
  val tokenize : tok list monad
  val tokenizeStream : string -> unit monad
end = struct
  structure T = MTSToken
  open MTSCFP
  type t = T.t
  type tok = TokenStream.item
  val whitespace = many space
  val ident =
    letter >>= (fn x => many alphanum >>= (fn xs =>
    let val s = String.implode (x::xs) in
      case T.makeKeyword s of
        SOME k => return k
      | NONE => return (T.makeIdentifier s) end))
  val integer =
    many1 digit >>= (fn x =>
      case T.makeInteger (String.implode x) of
       SOME i => return i | NONE => throwHere ([Err.Message "Int err"]))
  val sym =
    many1 (symbol) >>= (fn x => return (T.makeSymbol (String.implode x)))
  val leftpar = lpar >>= (fn x => return (T.makeLPar ()))
  val rightpar = rpar >>= (fn x => return (T.makeRPar ()))
  val token =
    position >>= (fn p =>
    (ident ++ sym ++ integer ++ leftpar ++ rightpar) >>= (fn x =>
    whitespace >>= (fn _ => return (p, x))))
  val tokenize =
    (many1 token >>= (fn ts => endOfInput >>= (fn _ => return ts)))
    ++ (throwHere ([]))
  fun tokenizeStream f =
    catch (
    getFileStream f >>= (fn cvs =>
    putstate cvs >>= (fn _ =>
    tokenize >>= (fn tl =>
    putTokenStream f (TokenStream.fromList tl) >>= (fn _ =>
    printMsg (String.concatWith " " (map TokenStream.stringOfElem tl)) >>= (fn _ =>
    printMsg (String.concat ["put stream ", Int.toString (List.length tl),
      "\n"]) >>= (fn _ =>
    return ())))))),
    (fn (p, r) => printMsg (S.stringOfPos p)))
      (*
        (case r of
        Err.Expected _ => printMsg "expected"
      | Err.Unexpected _ => printMsg "unexpected")))
      *)
end

