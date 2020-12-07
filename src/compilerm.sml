signature COMPILERM = sig
  include MONAD
  type var
  val eqv : var -> var -> bool
  type freshName = int
  type pts
  type err

  val getfvm : freshName monad
  val putfvm : freshName -> unit monad
  val getpts : pts monad
  val putpts : pts -> unit monad
  val throw : unit -> 'a monad
end

functor CompilerMT (structure C : sig
  type var
  val eqv : var -> var -> bool
  val varOfInt : int -> var
  type pts
  type err
end) : COMPILERM =
struct
  open C
  type var = var
  type freshName = int
  type pts = C.pts
  type err = unit

  structure FVM = StateFunctor (type s = freshName)
  structure PTS = StateT (type s = pts; structure M = FVM)
  structure EXC = ExceptionT (type e = err; structure M = PTS)
  open EXC

  val getfvm = lift (PTS.lift FVM.get)
  val putfvm =
    (fn st => lift (PTS.lift (FVM.put st)))
  val getpts = lift PTS.get
  val putpts = (fn st => lift (PTS.put st))
end

