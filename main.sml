use "common/common.sml";
use "common/monad.sml";
use "common/set.sml";
use "common/assoclist.sml";
use "common/freshvarmonad.sml";
use "parsercombinator/newpc.sml";
use "parsercombinator/charparser.sml";
use "src/syntax/lang/regionset.sml";
use "src/syntax/lang/ty.sml";
use "src/syntax/lang/term.sml";
use "src/syntax/lang/program.sml";
use "src/anf/lang/anfterm.sml";
use "src/anf/lang/anfprogram.sml";
use "src/anf/anf.sml";
use "src/closlang/lang/closlangterm.sml";
use "src/closlang/lang/closlangprogram.sml";
use "src/closlang/closlang.sml";
use "src/firstorder/lang/firstorderterm.sml";
use "src/firstorder/lang/firstorderprogram.sml";
use "src/x86/x86machine.sml";
use "src/x86/x86asm.sml";
use "src/syntax/tokenizer.sml";
use "src/syntax/parser.sml";
use "src/syntax/check.sml";

fun main () =
let
  val _ = PolyML.print_depth 100000
  (* val filename = List.nth (CommandLine.arguments (), 0) *)
  val filename = "examples/id.sml"
  val contents : CharVector.vector = TextIO.input (TextIO.openIn filename)
  val _ = PolyML.print contents
  val t = Tokenizer.tokenize { pos = (0, 0), s = { pos = 0, s = contents } }
  val _ = PolyML.print t
  val syn = SyntaxParser.program () t
  val _ = PolyML.print syn
  val _ = case syn of
    (TParser.Ok (s), _) =>
      let
        val _ = (PolyML.print (s); PolyML.print ("OK"))
        val _ = PolyML.print (TypeCheck.checkProgram s)
      in
        ()
      end
  | (TParser.Error (e), _) =>
      (PolyML.print (TErr.tostring e); PolyML.print ("NOT OK"); ())

  (* val _ = case syn of
    TParser.Ok (s, _) => 
    let
      val initstate1 = (s, EmptyEnv, [], Empty)
      val _ = PolyML.print (ANF.transformTerm s)
      val _ = PolyML.print initstate1
      val _ = PolyML.print (TypeCheck.runCheck s)
      val _ = PolyML.print (runToCompletion initstate1)
    in
      ()
    end
  | _ => () *)
in
  ()
end

