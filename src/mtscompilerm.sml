signature COMPILERM = sig
  include MONAD
  type var = MTS.var
  val eqv : var -> var -> bool
  type freshName = int
  type pts = MTS.sorts * MTS.ax * MTS.rules
  type err = unit
  type fileState = {
    fileStream : CharFileStream.stream option,
    tokenStream : TokenStream.stream option,
    syntaxTree : Syntax.toplvl list,
    coreAst : MTS.toplvl list
  }
  type compilerState = {
    files : (string * fileState) list,
    toplevelEnv : unit list
  }
  val getfvm : freshName monad
  val putfvm : freshName -> unit monad
  val getpts : pts monad
  val putpts : pts -> unit monad
  val getst : compilerState monad
  val putst : compilerState -> unit monad
  val throw : err -> 'a monad
  val newvar : var monad
  val getFile : string -> fileState monad
  val getFileStream : string -> CharFileStream.stream monad
  val getTokenStream : string -> TokenStream.stream monad
  val getSyntaxTree : string -> Syntax.toplvl list monad
  val getCoreAst : string -> MTS.toplvl list monad
  val updateFile : string -> (fileState -> fileState) -> unit monad
  val putFileName : string -> unit monad
  val putFileStream : string -> CharFileStream.stream -> unit monad
  val putTokenStream : string -> TokenStream.stream -> unit monad
  val putSyntaxTree : string -> Syntax.toplvl list -> unit monad
  val putCoreAst : string -> MTS.toplvl list -> unit monad
end

structure MTSCompilerM : COMPILERM = struct
  type var = MTS.var
  val eqv = MTS.eqv
  type freshName = int
  type pts = MTS.sorts * MTS.ax * MTS.rules
  type err = unit
  type fileState = {
    fileStream : CharFileStream.stream option,
    tokenStream : TokenStream.stream option,
    syntaxTree : Syntax.toplvl list,
    coreAst : MTS.toplvl list
  }
  type compilerState = {
    files : (string * fileState) list,
    toplevelEnv : unit list
  }
  val varOfInt = (fn i => MTS.GenVar i)
  structure FVM = StateFunctor (type s = freshName)
  structure ST = StateT (type s = compilerState; structure M = FVM)
  structure PTS = StateT (type s = pts; structure M = ST)
  structure EXC = ExceptionT (type e = err; structure M = PTS)
  open EXC
  val getfvm = lift (PTS.lift (ST.lift FVM.get))
  val putfvm = (fn st => lift (PTS.lift (ST.lift (FVM.put st))))
  val getpts = lift PTS.get
  val putpts = (fn st => lift (PTS.put st))
  val newvar = getfvm >>= (fn i => putfvm (i + 1) >>= (fn _ =>
    return (varOfInt i)))
  val getst = lift (PTS.lift ST.get)
  val putst = (fn st => lift (PTS.lift (ST.put st)))
  fun getFile n =
    getst >>= (fn ({ files = fs, toplevelEnv = tle }) =>
      (case List.find (fn (n', _) => n = n') fs of
        SOME (n', s) => return s
      | NONE => throw ()))
  fun getFileStream n =
    getFile n >>= (fn ({ fileStream = strm, tokenStream = _,
      syntaxTree = _, coreAst = _ }) =>
        case strm of SOME strm' => return strm' | NONE => throw ())
  fun getTokenStream n =
    getFile n >>= (fn ({ fileStream = _, tokenStream = strm,
      syntaxTree = _, coreAst = _ }) =>
        case strm of SOME strm' => return strm' | NONE => throw ())
  fun getSyntaxTree n =
    getFile n >>= (fn ({ fileStream = _, tokenStream = _,
      syntaxTree = synt, coreAst = _ }) => return synt)
  fun getCoreAst n =
    getFile n >>= (fn ({ fileStream = _, tokenStream = _,
      syntaxTree = _, coreAst = ast }) => return ast)
  fun updateFile n f =
    let fun update ([]) = throw ()
      | update ((n', s)::fs) =
        if n = n' then return ((n', f s)::fs)
        else update fs >>= (fn fs' => return ((n', s)::fs')) in
      getst >>= (fn ({ files = fs, toplevelEnv = tle }) =>
      update fs >>= (fn fs' => putst ({ files = fs, toplevelEnv = tle }))) end
  fun putFileName n =
    getst >>= (fn ({ files = fs, toplevelEnv = tle }) =>
      if List.exists (fn (n', _) => n = n') fs then return ()
      else putst ({files = fs @ [(n, { fileStream = NONE, tokenStream = NONE,
        syntaxTree = [], coreAst = [] })], toplevelEnv = tle}))
  fun putFileStream n strm =
    updateFile n (fn ({ fileStream = _, tokenStream = tstrm,
      syntaxTree = synt, coreAst = ast }) =>
        ({ fileStream = SOME strm, tokenStream = tstrm,
          syntaxTree = synt, coreAst = ast }))
  fun putTokenStream n strm =
    updateFile n (fn ({ fileStream = fstrm, tokenStream = _,
      syntaxTree = synt, coreAst = ast }) =>
        ({ fileStream = fstrm, tokenStream = SOME strm,
          syntaxTree = synt, coreAst = ast }))
  fun putSyntaxTree n tll =
    updateFile n (fn ({ fileStream = fstrm, tokenStream = tstrm,
      syntaxTree = synt, coreAst = ast }) =>
        ({ fileStream = fstrm, tokenStream = tstrm,
          syntaxTree = synt @ tll, coreAst = ast }))
  fun putCoreAst n tll =
    updateFile n (fn ({ fileStream = fstrm, tokenStream = tstrm,
      syntaxTree = synt, coreAst = ast }) =>
        ({ fileStream = fstrm, tokenStream = tstrm,
          syntaxTree = synt, coreAst = ast @ tll }))
end

structure TErr = struct
  type err = unit
  type pos = CharFileStream.pos
  type elem = CharFileStream.item
end

structure MTSCFP : sig
  include CHARPARSER
  val getFileStream : string -> CharFileStream.stream monad 
  val putTokenStream : string -> TokenStream.stream -> unit monad 
  end = struct
  structure CFP = CharFileParser (structure E = TErr; structure M = MTSCompilerM)
  open CFP
  fun getFileStream n =
    lift (PEXC.lift (PST.lift (MTSCompilerM.getFileStream n)))
  fun putTokenStream n ts =
    lift (PEXC.lift (PST.lift (MTSCompilerM.putTokenStream n ts)))
end

