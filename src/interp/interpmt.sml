signature INTERPM = sig
  include MONADZEROPLUS
  type var
  type enventry
  type env
  type s

  val getstate : s monad
  val putstate : s -> unit monad
  val ask : env monad
  val loc : (env -> env) -> 'a monad -> 'a monad
  val throw : unit -> 'a monad
  val inEnv : var -> env -> bool
  val isFresh : var -> unit monad
  val bindEntry : var -> enventry -> 'a monad -> 'a monad
  val bindMany : ((var * var) * enventry) list -> 'a monad -> 'a monad
  val getEntry : var -> enventry monad
  structure M : MONAD
end

functor InterpMT (structure S : sig
  type var
  type enventry
  type s
  type e
  val eqv : var -> var -> bool
end; structure M : MONAD) : INTERPM = struct
  structure M = M
  open S
  type var = var
  type enventry = enventry
  type env = (var * enventry) list
  structure IST = StateT (type s = s; structure M = M)
  structure IENV = ReaderT (type s = env; structure M = IST)
  structure IEXC = ExceptionT (type e = unit; structure M = IENV)
  structure IOPT = OptionT (structure M = IEXC)
  open IOPT

  val getstate = lift (IEXC.lift (IENV.lift IST.get))
  val putstate = (fn st => lift (IEXC.lift (IENV.lift (IST.put st))))
  val ask = lift (IEXC.lift IENV.ask)
  fun loc f m = (IENV.loc f) m
  fun throw () = IEXC.throw ()
  fun inEnv v e =
    List.exists (fn (v', x) => eqv v v') e
  fun isFresh v =
    ask >>= (fn e =>
    if inEnv v e then throw ()
    else return ())
  fun bindEntry v t =
    loc (fn e => (v, t)::e)
  fun bindMany ([]) m = m
  | bindMany (((v, v'), s)::xs) m =
    (bindEntry v' s (bindMany xs m))
  fun getEntry v =
    ask >>= (fn e =>
      case List.find (fn (v', x) => eqv v v') e of
        SOME (_, s) => return s
      | NONE => throw ())
end

