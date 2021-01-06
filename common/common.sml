signature TOSTRING =
sig
  type t
  val tostring : t -> string
end

datatype ('a, 'b) either =
  Left of 'a
| Right of 'b

fun debugPrint s =
  let val _ = TextIO.output (TextIO.stdOut, s)
    val _ = TextIO.flushOut TextIO.stdOut
  in () end

fun debugPrintline s =
  let val _ = TextIO.output (TextIO.stdOut, s)
    val _ = TextIO.output (TextIO.stdOut, "\n")
    val _ = TextIO.flushOut TextIO.stdOut
  in () end

