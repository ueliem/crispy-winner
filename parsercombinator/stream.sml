signature STREAM = sig
  type stream
  eqtype pos
  eqtype item
  val uncons : stream -> (item * stream) option
  val peek : stream -> item option
  val position : stream -> pos
  val eq : item * item -> bool
  val pcompare : pos * pos -> int
  val stringOfElem : item -> string
  val stringOfPos : pos -> string
  val isEmpty : stream -> bool
end

signature FILESTREAM = sig
  include STREAM where type pos = int * int
  type rawStream
  type rawPos = int
  val rawPosition : stream -> rawPos
end

functor MonoVectorStream (
  structure S : sig
    eqtype item
    include MONO_VECTOR where type elem = item
  end;
  val eq : S.item * S.item -> bool;
  val stringOfElem : S.item -> string
) : STREAM where type pos = int =
struct
  type pos = int
  type stream = { s : S.vector, pos : pos }
  type item = S.elem
  val eq = eq
  val stringOfElem = stringOfElem
  val stringOfPos = Int.toString
  fun uncons ({ s, pos }) = 
    let val len = S.length s
    in if pos < len then SOME (S.sub (s, pos),
                         { s = s, pos = pos + 1 })
      else NONE end
  fun peek ({ s, pos }) =
    let val len = S.length s
    in if pos < len then SOME (S.sub (s, pos))
      else NONE end
  fun position ({ s, pos }) = pos
  fun pcompare (p1, p2) =
    if p1 < p2 then ~1
    else if p1 = p2 then 0
    else 1
  fun isEmpty ({ s, pos }) = not (pos < S.length s)
end
