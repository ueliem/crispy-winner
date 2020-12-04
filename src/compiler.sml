structure Compiler : sig
  val loadFile : string -> CharFileStream.stream MTSCompilerM.monad
  val tokenizeStream : CharFileStream.stream -> TokenStream.stream MTSCompilerM.monad
  val compile : string -> unit MTSCompilerM.monad
end = struct
  open MTSCompilerM
  fun loadFile f =
    let val v = TextIO.inputAll (TextIO.openIn f)
    in return (CharFileStream.fromString v) end
  fun tokenizeStream cvs =
    Tokenizer.tokenize cvs >>= (fn (r, _) =>
    (case r of
      Tokenizer.CFP.PEXC.ExcVal (SOME tl) => return (TokenStream.fromList tl)
    | Tokenizer.CFP.PEXC.ExcVal NONE => throw ()
    | Tokenizer.CFP.PEXC.ExcErr e => throw ()))
  fun compile f =
    loadFile f >>= (fn cs =>
    tokenizeStream cs >>= (fn ts =>
    return ()))
end

