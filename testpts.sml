use "common/set.sml";
use "common/monad.sml";
use "common/assoclist.sml";
use "parsercombinator/pc.sml";
use "parsercombinator/charparser.sml";
use "src/spec.sml";
use "src/frontend/tokenizer.sml";
use "src/frontend/syntax.sml";
use "src/frontend/syntaxparser.sml";
use "src/syntax2core.sml";
use "src/core/pts.sml";
use "src/core/checkpts.sml";

open PTS
open FuncSpec

fun main() =
let
  val _ = PolyML.print_depth 100
  val seq = "val y : t = fn x : int => x + 1"
  val s = [IntSort, BoolSort, ProperType, Kind]
  val ax = [(IntSort, ProperType), (BoolSort, ProperType), (ProperType, Kind)]
  val rl = [
    (* (IntSort, IntSort, IntSort),
    (BoolSort, IntSort, IntSort),
    (IntSort, BoolSort, BoolSort),
    (BoolSort, BoolSort, BoolSort), *)
    (ProperType, ProperType, ProperType)
           ]
  val sp = (s, ax, rl)
  val prog1 = Abs (Sort IntSort, Variable (1))
  val prog2 = 
    App (Abs (Literal IntType, Variable (1)), Literal (IntLit 5))
  val t = TypeCheck.check_nat sp [] prog2 { deltas = [], errs = [] }
  val _ = PolyML.print t
  val filename = List.nth (CommandLine.arguments (), 0)
  val contents : CharVector.vector = TextIO.input (TextIO.openIn filename)
  val _ = PolyML.print contents
  val t = Tokenizer.tokenize { pos = 0, s = contents }
  val _ = PolyML.print t
  val syn = SyntaxParser.program () t
  val _ = PolyML.print syn
  val _ = case syn of
    TParser.Ok (s, _) => (PolyML.print (#1 (Syntax2Core.rename s 0)); ())
  | _ => ()
in
  ()
end

