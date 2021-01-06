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
