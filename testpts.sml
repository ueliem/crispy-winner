use "common/set.sml";
use "common/monad.sml";
use "common/assoclist.sml";
use "parsercombinator/pc.sml";
use "parsercombinator/charparser.sml";
use "src/frontend/tokenizer.sml";
use "src/frontend/syntax.sml";
use "src/frontend/syntaxparser.sml";
use "src/core/pts.sml";
use "src/core/checkpts.sml";

open PTS

fun main() =
let
  val _ = PolyML.print_depth 100
  val seq = "fn x : int => x + 1"
  val s = [ProperTypes, Kinds]
  val ax = [(ProperTypes, Kinds)]
  val rl = [(ProperTypes, ProperTypes, ProperTypes)]
  val sp = (s, ax, rl)
  val prog1 = Abs ("x", Literal IntType, Variable ("x", Literal IntType))
  val prog2 = Sort ProperTypes
  val t = TypeCheck.check sp [] prog1 { pairs = [], errs = [] }
  val _ = PolyML.print t
  val filename = List.nth (CommandLine.arguments (), 0)
  val contents = TextIO.input (TextIO.openIn filename)
  val _ = PolyML.print contents
in
  ()
end

