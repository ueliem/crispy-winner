infixr 2 >>=
infixr 1 ++

signature MONAD =
sig
  type 'a monad

  val return : 'a -> 'a monad

  val >>= : 'a monad * ('a -> 'b monad) -> 'b monad

end

signature MONADPLUSZERO =
sig
  include MONAD

  val ++ : 'a monad * 'a monad -> 'a monad

  val zero : 'a monad

end

signature MONADSTATE =
sig
  type state
  include MONAD where type 'a monad = state -> 'a * state

  val runState : 'a monad -> state -> 'a * state
  val get : state monad
  val put : state -> unit monad

end

signature FUNCTOR =
sig
  type 'a f
  val fmap : ('a -> 'b) -> 'a f -> 'b f
end

structure IdentityMonad : MONAD =
struct
  type 'a monad = 'a
  fun return x = x
  fun op >>= (m, f) = f m
end

functor StateFunctor (type s) :
sig
  datatype 'a state = State of s -> 'a * s
  include MONAD where type 'a monad = 'a state

  val runState : 'a state -> (s -> 'a * s)
  val get : s state
  val put : s -> unit state

end
=
struct
  datatype 'a state = State of s -> 'a * s
  type 'a monad = 'a state

  fun runState (State s) = s

  fun return x = State (fn s => (x, s))

  fun op >>= (m, f) = State (fn s =>
  let val (x, s') = runState m s
  in
    runState (f x) s'
  end)

  val get = State (fn s => (s, s))

  fun put s = State (fn _ => ((), s))
end

structure OptionMonad : MONADPLUSZERO =
struct
  type 'a monad = 'a option

  fun return x = SOME x

  fun op >>= (m, f) = 
    case m of
      SOME x => f x
    | NONE => NONE

  val zero = NONE

  fun op ++ (m1, m2) =
    case m1 of
      SOME x => SOME x
    | NONE => m2

end

functor ContinuationMonad (type r) : MONAD =
struct
  type 'a monad = ('a -> r) -> r

  fun return (a : 'a) = (fn (k : 'a -> r) => k a)

  fun op >>= (m, f) =
    (fn k => m (fn t => f t k))

end

functor OptionT (structure M : MONAD) :
sig
  include MONAD where type 'a monad = 'a option M.monad

  val lift : 'a M.monad -> 'a option M.monad

  val fail : unit -> 'a monad
end
=
struct
  type 'a monad = 'a option M.monad

  fun return x = M.return (SOME x)

  fun fail () = M.return NONE

  fun op >>= (m : 'a option M.monad, f : 'a -> 'b option M.monad) : 'b option M.monad = 
    M.>>= (m, (fn (x : 'a option) =>
      case x of
        SOME y => f y
      | NONE => M.return NONE
    ))

  fun lift (m : 'a M.monad) : 'a option M.monad =
    M.>>= (m, fn (x : 'a) =>
      M.return (SOME x)
    )

end

functor ContinuationT (type r; structure M : MONAD) : 
sig
  datatype 'a cont = Cont of ('a -> r M.monad) -> r M.monad

  include MONAD where type 'a monad = 'a cont
  include FUNCTOR where type 'a f = 'a cont

  val lift : 'a M.monad -> 'a monad

  val runCont : 'a monad -> (('a -> r M.monad) -> r M.monad)

  val callCC : (('a -> 'b monad) -> 'a monad) -> 'a monad

  val mapCont : (r M.monad -> r M.monad) -> 'a monad -> 'a monad

end
=
struct
  datatype 'a cont = Cont of ('a -> r M.monad) -> r M.monad

  type 'a monad = 'a cont
  type 'a f = 'a cont

  fun runCont (Cont c) = c

  fun return a = Cont (fn k => k a)

  fun op >>= (m, f) =
    Cont (fn k => runCont m (fn a => runCont (f a) k))

  fun lift a = 
    Cont ((fn b => M.>>= (a, b)))

  fun callCC (f : ('a -> 'b monad) -> 'a monad) = 
    Cont (fn k => runCont (f (fn a => Cont (fn _ => k a))) k)

  fun fmap f m =
    Cont (fn k => runCont m (k o f))

  fun mapCont f m = 
    Cont (fn k => f (runCont m k))

end

functor StateT (type s; structure M : MONAD) : 
sig
  datatype 'a state = State of s -> ('a * s) M.monad
  include MONAD where type 'a monad = 'a state

  val runState : 'a state -> (s -> ('a * s) M.monad)
  val lift : 'a M.monad -> s -> ('a * s) M.monad
  val get : s state
  val put : s -> unit state

end
=
struct
  datatype 'a state = State of s -> ('a * s) M.monad
  type 'a monad = 'a state
  type 'a f = 'a state

  fun runState (State s) = s

  fun return x = State (fn s => M.return (x, s))

  fun op >>= (m, f) = 
    State (fn s =>
      op M.>>= (runState m s, (fn (x, s') => 
        runState (f x) s'
      )))

  fun lift m s = 
    op M.>>= (m, (fn x => M.return (x, s)))

  val get = State (fn s => M.return (s, s))

  fun put s = State (fn _ => M.return ((), s))

end

