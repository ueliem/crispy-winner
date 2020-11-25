signature STREAM = sig
  type stream
  type pos
  type elem
  val uncons : stream -> (elem * stream) option
  val peek : stream -> elem option
  val position : stream -> pos
  val eq : elem * elem -> bool
  val pcompare : pos * pos -> int
  val stringOfElem : elem -> string
  val stringOfPos : pos -> string
end

signature FILESTREAM = sig
  include STREAM
  type rawStream
  type rawPos
  val rawPosition : stream -> rawPos
end

functor MonoVectorStream (
  structure S : MONO_VECTOR;
  val eq : S.elem * S.elem -> bool;
  val stringOfElem : S.elem -> string
) : STREAM =
struct
  type pos = int
  type stream = { s : S.vector, pos : pos }
  type elem = S.elem
  val eq = eq
  val stringOfElem = stringOfElem
  val stringOfPos = Int.toString

  fun uncons (strm) = 
    let val pos = #pos strm
      val len = S.length (#s strm)
    in if pos < len then SOME (S.sub (#s strm, pos),
                         { s = #s strm, pos = pos + 1 })
      else NONE end

  fun peek (strm) =
    let val pos = #pos strm
      val len = S.length (#s strm)
    in if pos < len then SOME (S.sub (#s strm, pos))
      else NONE end

  fun position (strm) = #pos strm
  fun pcompare (p1, p2) =
    if p1 < p2 then ~1
    else if p1 = p2 then 0
    else 1
end

structure CharVectorStream =
  MonoVectorStream (structure S = CharVector;
    val eq = (fn (x, y) => x = y);
    val stringOfElem = Char.toString)

structure CharFileStream : sig
  include FILESTREAM
  structure CS : STREAM
end = struct
  structure CS = CharVectorStream
  type rawStream = CS.stream
  type rawPos = CS.pos
  type pos = int * int
  type stream = { s : rawStream, pos : pos }
  type elem = CS.elem
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

  fun peek (strm) = CS.peek (#s strm)

  fun position ({ s, pos }) = pos
  fun rawPosition ({ s, pos }) = #pos s
  fun pcompare ((l1, c1), (l2, c2)) =
    if l1 < l2 then ~1
    else if l1 = l2 then
      if c1 < c2 then ~1
      else if c1 = c2 then 0
      else 1
    else 1
end

