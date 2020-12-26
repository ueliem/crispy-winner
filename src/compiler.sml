structure Compiler : sig
  val loadFile : string -> CharFileStream.stream MTSCompilerM.monad
  val tokenizeStream : string -> unit MTSCompilerM.monad
  val parseStream : string -> unit MTSCompilerM.monad
  val compile : string -> unit MTSCompilerM.monad
end = struct
  open MTSCompilerM
  fun loadFile f =
    let val v = TextIO.inputAll (TextIO.openIn f) in
      putFileStream f (CharFileStream.fromString v) >>= (fn _ =>
      return (CharFileStream.fromString v)) end
  fun tokenizeStream f =
    MTSTokenizer.tokenizeStream f CharFileStream.emptyStream
      >>= (fn (r, _) => (case r of
        MTSCFP.PEXC.ExcVal (SOME ()) => return ()
      | MTSCFP.PEXC.ExcVal NONE => throw ()
      | MTSCFP.PEXC.ExcErr e => throw ()))
  fun parseStream f =
    SyntaxParser.parseStream f TokenStream.emptyStream
      >>= (fn (r, _) => (case r of
        SyntaxParser.TSP.PEXC.ExcVal (SOME _) => return ()
      | SyntaxParser.TSP.PEXC.ExcVal NONE => throw ()
      | SyntaxParser.TSP.PEXC.ExcErr e => throw ()))
  fun compile f =
    loadFile f >>= (fn cs =>
    tokenizeStream f >>= (fn () =>
    parseStream f >>= (fn () =>
    return ())))
end

