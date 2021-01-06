infix 2 >>= >>
infix 1 ++

signature MONAD = sig
  type 'a monad
  val return : 'a -> 'a monad
  val >>= : 'a monad * ('a -> 'b monad) -> 'b monad
end

signature MONADZERO = sig
  include MONAD
  val zero : unit -> 'a monad
end

signature MONADPLUS = sig
  include MONAD
  val ++ : 'a monad * 'a monad -> 'a monad
end
signature MONADZEROPLUS = sig
  include MONADZERO
  val ++ : 'a monad * 'a monad -> 'a monad
end

signature FUNCTOR = sig
  type 'a f
  val fmap : ('a -> 'b) -> 'a f -> 'b f
end

signature MONADT = sig
  type 'a monad
  structure M : MONAD
  val lift : 'a M.monad -> 'a monad
end

structure IdentityMonad : MONAD = struct
  type 'a monad = 'a
  fun return x = x
  fun op >>= (m, f) = f m
end

signature MUTIL = sig
  include MONAD
  val liftM : ('a -> 'b) -> 'a monad -> 'b monad
  val >> : ('a monad * 'b monad) -> 'b monad
  val sequence : 'a monad list -> 'a list monad
  val mapM : ('a -> 'b monad) -> 'a list -> 'b list monad
  val foldM : ('a -> 'b -> 'a monad) -> 'a -> 'b list -> 'a monad
end

functor MUtil (structure M : MONAD) : MUTIL = struct
  open M

  fun liftM f m = m >>= (fn x => return (f x))
  fun op >> (m1, m2) = M.>>= (m1, (fn _ => m2))
  fun sequence ([]) = return []
  | sequence (x::xs) =
      x >>= (fn x' => sequence xs >>= (fn xs' => return (x'::xs')))
  fun mapM f xs = sequence (map f xs)
  fun foldM f y [] = return y
  | foldM f y (x::xs) = f y x >>= (fn z => foldM f z xs)
end

