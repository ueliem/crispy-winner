functor FreshVarMonad (type v; val f : int -> v) :
sig
  include MONAD
  val fresh : v monad
end
=
struct
  structure State = StateFunctor (type s = int)
  open State

  val fresh =
    State.get >>= (fn i =>
    State.put (i + 1) >>= (fn _ =>
      return (f i)
    ))

end

