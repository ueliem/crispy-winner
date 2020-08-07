structure CharStream =
  StreamFunctor (structure S = CharVector;
    val eq = (fn (x, y) => x = y);
    val estr = (fn x => Char.toString x))

structure CharFileStream :
sig
  include STRM
  structure CS : STRM
end
=
struct
  structure CS = CharStream
  type pos = int * int
  type stream = { s : CS.stream, pos : pos }
  type elem = CS.elem

  fun uncons (strm) = 
  let
    val (row, col) = #pos strm
  in
    (case CS.uncons (#s strm) of
      SOME (c, s') =>
        (case c of
          #"\n" => SOME (c, { s = s', pos = (row + 1, col) })
        | _ => SOME (c, { s = s', pos = (row, col + 1) }))
    | NONE => NONE)
  end

  fun position (strm) = #pos strm

  val equiv = CS.equiv

  fun pcompare ((l1, c1), (l2, c2)) =
    if l1 < l2 then ~1
    else if l1 = l2 then
      if c1 < c2 then ~1
      else if c1 = c2 then 0
      else 1
    else 1

  val elem_to_string = CS.elem_to_string

  fun pos_to_string (l, c) =
    String.concat ["line ", Int.toString l, " column ", Int.toString c]

  fun peek (strm) = CS.peek (#s strm)

end

(* structure CParser = ParserT(structure S = CharStream) *)

functor CharParser (structure S : sig
  include STRM
  where type elem = char
end)
(* sig
  structure CParser
end
=
struct
  structure CParser = ParserT(structure S = S)
end
*)
(* structure CharParser : 
sig
  val satisfies : (char -> bool) -> char CParser.Parser
  val lpar : unit -> char CParser.Parser
  val rpar : unit -> char CParser.Parser
  val lcurly : unit -> char CParser.Parser
  val rcurly : unit -> char CParser.Parser
  val comma : unit -> char CParser.Parser
  val symbol : unit -> char CParser.Parser
  val digit : unit -> char CParser.Parser
  val letter : unit -> char CParser.Parser
  val alphanum : unit -> char CParser.Parser
  val space : unit -> char CParser.Parser
end*)
=
struct
  structure CErr = StreamError(structure S = S)
  structure CParser = ParserT(structure S = S; structure E = CErr)
  open CParser

  val symbols = [#"+", #"-", #"*", #"/", #"=", #">", #"<", #":"]

  (* fun any () =
    (fn (s : CharStream.stream) =>
      (case CharStream.uncons s of
        SOME (x, xs) => CParser.Ok (x, xs)
      | NONE => fail s)) *)

  fun satisfies f = 
    next () >>= (fn x =>
    if f x then return x else fail ())

  fun lpar () = satisfies (fn x => x = #"(")

  fun rpar () = satisfies (fn x => x = #")")

  fun lcurly () = satisfies (fn x => x = #"{")

  fun rcurly () = satisfies (fn x => x = #"}")

  fun symbol () = satisfies (fn x => List.exists (fn y => x = y) symbols)

  fun comma () = satisfies (fn x => x = #",")

  fun digit () = satisfies Char.isAlphaNum

  fun letter () = satisfies Char.isAlpha
    
  fun alphanum () = satisfies Char.isAlphaNum

  fun space () = satisfies Char.isSpace
end

structure VectorCharParser = CharParser (structure S = CharStream)
structure FileCharParser = CharParser (structure S = CharFileStream)

