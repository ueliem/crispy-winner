structure CharStream = StreamFunctor (CharVector)
structure CParser = ParserFunctor(CharStream)

structure CharParser : 
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
end
=
struct
  open CParser

  val symbols = [#"+", #"-", #"*", #"/", #"=", #">", #"<", #":"]

  fun any () =
    (fn (s : CharStream.stream) =>
      (case CharStream.uncons s of
        SOME (x, xs) => CParser.Ok (x, xs)
      | NONE => fail s))

  fun satisfies f = 
    any () >>= (fn x =>
    if f x then return x else fail)

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

