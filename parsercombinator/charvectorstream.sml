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
