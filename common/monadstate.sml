signature STATE = sig
  type s
  include MONAD (* where type 'a monad = s -> 'a * s *)
  val get : s monad
  val put : s -> unit monad
end

signature STATET = sig
  include STATE
  structure M : MONAD
  val lift : 'a M.monad -> 'a monad
end

functor StateFunctor (type s) : sig
  include STATE
end = struct
  type s = s
  type 'a state = s -> 'a * s
  type 'a monad = 'a state
  fun return x = (fn s => (x, s))
  fun op >>= (m, f) = (fn s =>
    let val (x, s') = m s
    in
      (f x) s'
    end)
  val get = (fn s => (s, s))
  fun put s = (fn _ => ((), s))
end

functor StateT (type s; structure M : MONAD) : sig
  include STATET
end = struct
  structure M = M
  type s = s
  type 'a state = s -> ('a * s) M.monad
  type 'a monad = 'a state
  type 'a f = 'a state
  fun return x = (fn s => M.return (x, s))
  fun op >>= (m, f) = 
    (fn s =>
      op M.>>= (m s, (fn (x, s') => 
        (f x) s'
      )))
  fun lift m s = 
    op M.>>= (m, (fn x => M.return (x, s)))
  val get = (fn s => M.return (s, s))
  fun put s = (fn _ => M.return ((), s))
end

