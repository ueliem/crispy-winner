signature EXCEPTIONT = sig
  structure M : MONAD
  type e
  datatype 'a except =
    ExcVal of 'a
  | ExcErr of e
  include MONAD where type 'a monad = 'a except M.monad
  val lift : 'a M.monad -> 'a monad
  val throw : e -> 'a monad
  val catch : 'a monad -> (e -> 'a monad) -> 'a monad
  val run : 'a monad -> (('a, e) either) M.monad
end

functor ExceptionT (type e; structure M : MONAD) : EXCEPTIONT = struct
  structure M = M
  type e = e
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
  fun catch m f =
    M.>>= (m, (fn x => (case x of
      ExcVal v => M.return (ExcVal v)
    | ExcErr err => f err)))
  fun run m =
    M.>>= (m, (fn x => case x of
      ExcVal v => M.return (Left v)
    | ExcErr err => M.return (Right err)))
end

