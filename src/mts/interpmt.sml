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
end

functor InterpMT (structure S : sig
  type var
  type enventry
  type s
  type e
  val eqv : var -> var -> bool
end) : INTERPM =
struct
  open S
  type var = var
  type enventry = enventry
  type env = (var * enventry) list
  structure M = StateFunctor (type s = s)
  structure MM = ReaderT (type s = env; structure M = M)
  structure MMM = ExceptionT (type e = unit; structure M = MM)
  structure MMMM = OptionT (structure M = MMM)
  open MMMM

  val getstate = lift (MMM.lift (MM.lift M.get))

  val putstate = (fn st => lift (MMM.lift (MM.lift (M.put st))))

  val ask = lift (MMM.lift MM.ask)

  fun loc f m = (MM.loc f) m

  fun throw () = MMM.throw ()

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

