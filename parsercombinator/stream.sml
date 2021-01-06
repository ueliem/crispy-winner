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

structure CharVectorStream : sig
  include STREAM
  val fromString : string -> stream
end = struct
  structure SS = struct
    type item = char
    open CharVector
  end
  structure MVS = MonoVectorStream (structure S = SS;
    val eq = (fn (x, y) => x = y);
    val stringOfElem = Char.toString)
  open MVS
  fun fromString s = ({ s = s, pos = 0 })
end

structure CharFileStream : sig
  include FILESTREAM
  structure CS : STREAM
  val emptyStream : stream
  val fromString : string -> stream
end = struct
  structure CS = CharVectorStream
  type rawStream = CS.stream
  type rawPos = CS.pos
  type pos = int * int
  type stream = { s : rawStream, pos : pos }
  type item = CS.item
  val eq = CS.eq
  val stringOfElem = CS.stringOfElem
  fun stringOfPos (l, c) =
    String.concat ["line ", Int.toString l, " column ", Int.toString c]
  fun uncons ({ s, pos }) = 
    let val (row, col) = pos
    in (case CS.uncons s of
      SOME (c, s') =>
        (case c of
          #"\n" => SOME (c, { s = s', pos = (row + 1, 0) })
        | _ => SOME (c, { s = s', pos = (row, col + 1) }))
    | NONE => NONE) end

  fun peek ({ s, pos }) = CS.peek s
  fun position ({ s, pos }) = pos
  fun rawPosition ({ s, pos }) = CS.position s
  fun pcompare ((l1, c1), (l2, c2)) =
    if l1 < l2 then ~1
    else if l1 = l2 then
      if c1 < c2 then ~1
      else if c1 = c2 then 0
      else 1
    else 1
  val emptyStream = ({ pos = (0, 0), s = CS.fromString "" })
  fun fromString s = ({ pos = (0, 0), s = CS.fromString s })
  fun isEmpty ({ s, pos }) = CS.isEmpty s
end

