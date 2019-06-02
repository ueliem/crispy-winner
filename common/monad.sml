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

functor StateFunctor (type s) : MONADSTATE =
struct
  type state = s
  type 'a monad = state -> 'a * state

  fun return x = (fn s => (x, s))

  fun op >>= (m, f) = (fn s =>
  let val (x, s') = m s
  in
    f x s'
  end)

  fun runState m s = m s

  fun get s = (s, s)

  fun put s = (fn _ => ((), s))
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

