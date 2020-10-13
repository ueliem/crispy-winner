structure Defs : sig
  include MONADZEROPLUS where type 'a monad = 'a InterpM.monad
  val checkDefs : MTS.def -> MTS.term monad
end
=
struct
  open InterpM
  open MTS
  open MTSCheck

  (* type valdef = var * term * term
  type datadef = name * term * (name * term) list
  type newtydef = name * term
  type classdef = name * (name * term) list
  type instancedef = name * name * (name * term) list *)

  fun bindManyTy ([]) next = next
  | bindManyTy ((v, m)::ml) next =
      bindTy v m (bindManyTy ml next)

  fun checkMany ([]) = return []
  | checkMany ((c, m)::dconml') =
      whsdcl m >>= (fn m' =>
      checkMany dconml' >>= (fn ml =>
      return (m'::ml)))

  fun checkDefs (DefEnd) = raise Fail ""
  | checkDefs (DefVal ((v, m1, m2), next)) =
      bindDel v m1 m2 (sdcl m2 >>= (fn m2' =>
      bequiv m1 m2' >>= (fn _ =>
      checkDefs next)))
  | checkDefs (DefData ((tcon, tm, dconml), next)) =
      whsdcl tm >>= (fn s =>
      isSort s >>= (fn s' =>
        let
          val dconml' = map (fn (n, m) => (NamedVar n, m)) dconml
        in
          bindManyTy (((NamedVar tcon), tm)::dconml') (checkDefs next)
        end))
  | checkDefs (DefNewTy ((tcon, tm), next)) = raise Fail ""
  | checkDefs (DefClass ((v, m, vml), next)) = raise Fail ""
  | checkDefs (DefInstance (_, next)) = raise Fail ""

end
