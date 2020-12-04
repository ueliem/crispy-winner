signature READERT = sig
  structure M : MONAD
  type s
  include MONAD where type 'a monad = s -> 'a M.monad
  val lift : 'a M.monad -> 'a monad
  val ask : s monad
  val loc : (s -> s) -> 'a monad -> 'a monad
  val asks : (s -> 'a) -> 'a monad
end

functor ReaderT (type s; structure M : MONAD) : READERT = struct
  type s = s
  structure M = M
  type 'a monad = s -> 'a M.monad
  fun return a e = M.return a
  fun op >>= (m, f) = 
    (fn e =>
      op M.>>= (m e, (fn a => 
        f a e
      )))
  fun lift a e = a
  val ask = M.return (* (fn e => return e e) *)
  fun loc f m = (fn e => m (f e))
  fun asks f = ask >>= (fn e => return (f e))
end

