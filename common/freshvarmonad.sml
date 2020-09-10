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
    State.get >>= (fn i => return (f i))

end

