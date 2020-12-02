signature COMPILERM = sig
  include MONADZEROPLUS
  type var
  val eqv : var -> var -> bool
  type enventry
  type env
  type freshName = int
  type pts
  type err

  val getfvm : freshName monad
  val putfvm : freshName -> unit monad
  val getpts : pts monad
  val putpts : pts -> unit monad
  val ask : env monad
  val loc : (env -> env) -> 'a monad -> 'a monad
  val throw : unit -> 'a monad
  val inEnv : var -> env -> bool
  val isFresh : var -> unit monad
  val bindEntry : var -> enventry -> 'a monad -> 'a monad
  val bindMany : ((var * var) * enventry) list -> 'a monad -> 'a monad
  val getEntry : var -> enventry monad
end

functor CompilerMT (structure C : sig
  type var
  val eqv : var -> var -> bool
  val varOfInt : int -> var
  type enventry
  type pts
  type err
end) : COMPILERM =
struct
  open C
  type var = var
  type enventry = enventry
  type env = (var * enventry) list
  type freshName = int
  type pts = C.pts
  type err = unit

  structure STM = StateFunctor (type s = freshName)
  structure FVM = StateFunctor (type s = freshName)
  structure PTS = StateT (type s = pts; structure M = FVM)
  structure ENV = ReaderT (type s = env; structure M = PTS)
  structure EXC = ExceptionT (type e = err; structure M = ENV)
  structure OPT = OptionT (structure M = EXC)
  open OPT

  val getfvm = lift (EXC.lift (ENV.lift (PTS.lift FVM.get)))
  val putfvm =
    (fn st => lift (EXC.lift (ENV.lift (PTS.lift (FVM.put st)))))
  val getpts = lift (EXC.lift (ENV.lift (PTS.get)))
  val putpts = (fn st => lift (EXC.lift (ENV.lift (PTS.put st))))
  val ask = lift (EXC.lift ENV.ask)
  fun loc f m = (ENV.loc f) m
  fun throw () = EXC.throw ()
  fun inEnv v e = List.exists (fn (v', x) => eqv v v') e
  fun isFresh v =
    ask >>= (fn e =>
    if inEnv v e then throw ()
    else return ())
  fun bindEntry v t = loc (fn e => (v, t)::e)
  fun bindMany ([]) m = m
  | bindMany (((v, v'), s)::xs) m =
    (bindEntry v' s (bindMany xs m))
  fun getEntry v =
    ask >>= (fn e =>
      case List.find (fn (v', x) => eqv v v') e of
        SOME (_, s) => return s
      | NONE => throw ())
end

