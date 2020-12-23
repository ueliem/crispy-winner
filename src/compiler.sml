structure Compiler : sig
  val loadFile : string -> CharFileStream.stream MTSCompilerM.monad
  val tokenizeStream : CharFileStream.stream
    -> TokenStream.stream MTSCompilerM.monad
  val compile : string -> unit MTSCompilerM.monad
end = struct
  open MTSCompilerM
  fun loadFile f =
    let val v = TextIO.inputAll (TextIO.openIn f)
    in return (CharFileStream.fromString v) end
  fun tokenizeStream cvs =
    MTSTokenizer.tokenize cvs >>= (fn (r, _) =>
    (case r of
      MTSCFP.PEXC.ExcVal (SOME tl) =>
        return (TokenStream.fromList tl)
    | MTSCFP.PEXC.ExcVal NONE => throw ()
    | MTSCFP.PEXC.ExcErr e => throw ()))
  fun parseStream tvs =
    SyntaxParser.ptsTerm () tvs >>= (fn (r, _) =>
    (case r of
      SyntaxParser.TSP.PEXC.ExcVal (SOME _) => return ()
    | SyntaxParser.TSP.PEXC.ExcVal NONE => throw ()
    | SyntaxParser.TSP.PEXC.ExcErr e => throw ()))
  fun compile f =
    loadFile f >>= (fn cs =>
    tokenizeStream cs >>= (fn ts =>
    parseStream ts >>= (fn () =>
    return ())))
end

