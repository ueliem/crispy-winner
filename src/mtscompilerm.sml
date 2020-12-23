(* structure MTSCompilerM = CompilerMT (structure C = struct
  type var = MTS.var
  val eqv = MTS.eqv
  val varOfInt = (fn i => MTS.GenVar i)
  type enventry = MTS.specification
  type pts = MTS.sorts * MTS.ax * MTS.rules
  type err = unit
end)
*)
signature COMPILERM = sig
  include MONAD
  type var = MTS.var
  val eqv : var -> var -> bool
  type freshName = int
  type pts = MTS.sorts * MTS.ax * MTS.rules
  type err = unit
  type fileState = {
    fileName : string,
    syntaxTree : Syntax.toplvl list,
    coreAst : MTS.toplvl list
  }
  type compilerState = {
    files : fileState list,
    toplevelEnv : unit list
  }

  val getfvm : freshName monad
  val putfvm : freshName -> unit monad
  val getpts : pts monad
  val putpts : pts -> unit monad
  val throw : err -> 'a monad
  val newvar : var monad
end

structure MTSCompilerM : COMPILERM = struct
  type var = MTS.var
  val eqv = MTS.eqv
  type freshName = int
  type pts = MTS.sorts * MTS.ax * MTS.rules
  type err = unit
  type fileState = {
    fileName : string,
    syntaxTree : Syntax.toplvl list,
    coreAst : MTS.toplvl list
  }
  type compilerState = {
    files : fileState list,
    toplevelEnv : unit list
  }
  val varOfInt = (fn i => MTS.GenVar i)

  structure FVM = StateFunctor (type s = freshName)
  structure ST = StateFunctor (type s = compilerState)
  structure PTS = StateT (type s = pts; structure M = FVM)
  structure EXC = ExceptionT (type e = err; structure M = PTS)
  open EXC

  val getfvm = lift (PTS.lift FVM.get)
  val putfvm = (fn st => lift (PTS.lift (FVM.put st)))
  val getpts = lift PTS.get
  val putpts = (fn st => lift (PTS.put st))
  val newvar = getfvm >>= (fn i => putfvm (i + 1) >>= (fn _ =>
    return (varOfInt i)))
end

structure TErr = struct
  type err = unit
  type pos = CharFileStream.pos
  type elem = CharFileStream.item
end

structure MTSCFP = CharFileParser (structure E = TErr; structure M = MTSCompilerM)

