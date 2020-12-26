structure MTSTokenizer : sig
  include CHARPARSER
  type t = MTSToken.t
  type tok = TokenStream.item
  val whitespace : char list monad
  val keyword : t monad
  val ident : t monad
  val integer : t monad
  val sym : t monad
  val leftpar : t monad
  val rightpar : t monad
  val token : tok monad
  val tokenize : tok list monad
  val tokenizeStream : string -> unit monad
  (* val tokstr : string -> unit MTSCompilerM.monad *)
end = struct
  structure T = MTSToken
  structure TE = TErr
  structure M = MTSCompilerM
  open MTSCFP
  type t = T.t
  type tok = TokenStream.item
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
  fun tokenizeStream f =
    getFileStream f >>= (fn cvs =>
    putstate cvs >>= (fn _ =>
    tokenize >>= (fn tl =>
    putTokenStream f (TokenStream.fromList tl) >>= (fn _ =>
    return ()))))
  
  (* fun tokstr f =
    (op M.>>=
      (tokenizeStream f,
      (fn r => (case r of
        (SOME ()) => MTSCompilerM.return ()
      | NONE => MTSCompilerM.throw () ))))
        (* { pos = (0, 0), s = { pos = 0, s = "" } } *)
        *)

    (*
    * op M.>>= (getFileStream f, (fn cvs =>
    op M.>>= (tokenize cvs, (fn (r, _) => (case r of
      PEXC.ExcVal (SOME tl) =>
        op M.>>= (putTokenStream f (TokenStream.fromList tl), (fn _ =>
        M.return (TokenStream.fromList tl)))
    | PEXC.ExcVal NONE => throw ()
    | PEXC.ExcErr e => throw ())))))
    *)
end

