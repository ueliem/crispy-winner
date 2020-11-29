infixr 2 >>= >>
infixr 1 ++

signature MONAD = sig
  type 'a monad
  val return : 'a -> 'a monad
  val >>= : 'a monad * ('a -> 'b monad) -> 'b monad
end

signature MONADZERO = sig
  include MONAD
  val zero : unit -> 'a monad
end

signature MONADZEROPLUS = sig
  include MONADZERO
  val ++ : 'a monad * 'a monad -> 'a monad
end

signature MONADSTATE = sig
  type s
  include MONAD (* where type 'a monad = s -> 'a * s *)
  val get : s monad
  val put : s -> unit monad
end

signature FUNCTOR = sig
  type 'a f
  val fmap : ('a -> 'b) -> 'a f -> 'b f
end

structure IdentityMonad : MONAD = struct
  type 'a monad = 'a
  fun return x = x
  fun op >>= (m, f) = f m
end

functor StateFunctor (type s) : sig
  (* type 'a state = s -> 'a * s
  include MONAD where type 'a monad = 'a state
  val get : s state
  val put : s -> unit state *)
  include MONADSTATE
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

structure OptionMonad : MONADZEROPLUS =
struct
  type 'a monad = 'a option
  fun return x = SOME x
  fun op >>= (m, f) = 
    case m of
      SOME x => f x
    | NONE => NONE
  val zero = (fn _ => NONE)
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
  include MONADZEROPLUS where type 'a monad = 'a option M.monad
  val lift : 'a M.monad -> 'a option M.monad
end = struct
  type 'a monad = 'a option M.monad
  fun return x = M.return (SOME x)
  fun op >>= (m : 'a option M.monad, f : 'a -> 'b option M.monad) : 'b option M.monad = 
    M.>>= (m, (fn (x : 'a option) =>
      case x of
        SOME y => f y
      | NONE => M.return NONE))
  fun lift (m : 'a M.monad) : 'a option M.monad =
    M.>>= (m, fn (x : 'a) => M.return (SOME x))
  val zero = (fn _ => M.return NONE)
  fun op ++ (m1, m2) =
    M.>>= (m1, (fn (x : 'a option) =>
      case x of
        SOME y => M.return (SOME y)
      | NONE =>
          M.>>= (m2, (fn (z : 'a option) =>
            case z of
              SOME y => M.return (SOME y)
            | NONE => M.return NONE))))
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

functor StateT (type s; structure M : MONAD) : sig
  (* type 'a state = s -> ('a * s) M.monad
  include MONAD where type 'a monad = 'a state
  val lift : 'a M.monad -> s -> ('a * s) M.monad
  val get : s state
  val put : s -> unit state *)
  include MONADSTATE
end = struct
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

functor ReaderT (type s; structure M : MONAD) : sig
  include MONAD where type 'a monad = s -> 'a M.monad
  val lift : 'a M.monad -> 'a monad
  val ask : s monad
  val loc : (s -> s) -> 'a monad -> 'a monad
  val asks : (s -> 'a) -> 'a monad
end = struct
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

functor ExceptionT (type e; structure M : MONAD) : sig
  datatype 'a except =
    ExcVal of 'a
  | ExcErr of e
  include MONAD where type 'a monad = 'a except M.monad
  val lift : 'a M.monad -> 'a monad
  val throw : e -> 'a monad
end = struct
  datatype 'a except =
    ExcVal of 'a
  | ExcErr of e
  type 'a monad = 'a except M.monad
  fun return x = M.return (ExcVal x)
  fun op >>= (m, f) =
    M.>>= (m, (fn x =>
      (case x of
        ExcVal x' => f x'
      | ExcErr x' => M.return (ExcErr x'))))
  fun lift m = M.>>= (m, (fn x => M.return (ExcVal x)))
  fun throw e = M.return (ExcErr e)
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

