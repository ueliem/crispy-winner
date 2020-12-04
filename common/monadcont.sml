functor ContinuationMonad (type r) : MONAD =
struct
  type 'a monad = ('a -> r) -> r
  fun return (a : 'a) = (fn (k : 'a -> r) => k a)
  fun op >>= (m, f) =
    (fn k => m (fn t => f t k))
end

functor ContinuationT (type r; structure M : MONAD) : sig
  datatype 'a cont = Cont of ('a -> r M.monad) -> r M.monad
  include MONAD where type 'a monad = 'a cont
  include FUNCTOR where type 'a f = 'a cont
  val lift : 'a M.monad -> 'a monad
  val runCont : 'a monad -> (('a -> r M.monad) -> r M.monad)
  val callCC : (('a -> 'b monad) -> 'a monad) -> 'a monad
  val mapCont : (r M.monad -> r M.monad) -> 'a monad -> 'a monad
end = struct
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

