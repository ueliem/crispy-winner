structure Compiler : sig
  val loadFile : string -> CharFileStream.stream MTSCompilerM.monad
  val tokenizeStream : string -> unit MTSCompilerM.monad
  (* val parseStream : string -> unit MTSCompilerM.monad *)
  val compile : string -> unit MTSCompilerM.monad
end = struct
  open MTSCompilerM
  fun loadFile f =
    let val v = TextIO.inputAll (TextIO.openIn f) in
      printMsg v >>= (fn _ =>
      putFileName f >>= (fn _ =>
      putFileStream f (CharFileStream.fromString v) >>= (fn _ =>
      printMsg "loaded file" >>= (fn _ =>
      return (CharFileStream.fromString v))))) end
  fun tokenizeStream f =
    MTSTokenizer.tokenizeStream f CharFileStream.emptyStream
      >>= (fn (r, _) => (case r of
        MTSCFP.PEXC.ExcVal () => return ()
      | MTSCFP.PEXC.ExcErr e => throw (TokenizerError)))
  fun parseStream f =
    SyntaxParser.parseStream f TokenStream.emptyStream
      >>= (fn (r, _) => (case r of
        SyntaxParser.PEXC.ExcVal () => return ()
      | SyntaxParser.PEXC.ExcErr e => throw (SyntaxError)))
  fun compile f =
    catch (loadFile f >>= (fn cs =>
    tokenizeStream f >>= (fn () =>
    parseStream f >>= (fn () =>
    return ()))), (fn r =>
      (case r of
        CompilerError s => printMsg "CompilerError: " >>= (fn _ =>
          printMsg s >>= (fn _ =>
          printMsg "\n" >>= (fn _ => return ())))
      | TokenizerError => printMsg "TokenizerError"
      | SyntaxError => printMsg "SyntaxError")))
end

