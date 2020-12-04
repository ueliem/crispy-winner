signature OPTION = sig
  include MONADZEROPLUS
end

signature OPTIONT = sig
  include OPTION
  structure M : MONAD
  val lift : 'a M.monad -> 'a monad
end

structure OptionMonad : OPTION =
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

functor OptionT (structure M : MONAD) :
sig
  include OPTIONT
end = struct
  structure M = M
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


