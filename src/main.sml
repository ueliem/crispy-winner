use "common/common.sml";
use "common/monad.sml";
use "src/compilerm.sml";
use "parsercombinator/stream.sml";
use "parsercombinator/pc.sml";
use "parsercombinator/charparser.sml";
use "src/mts/interpmt.sml";

use "src/mts/lang/mts.sml";
use "src/mts/lang/subst.sml";
use "src/mts/lang/alphaequiv.sml";
use "src/syntax/tokenizer.sml";
use "src/syntax/tokenparser.sml";
use "src/syntax/syntaxparser.sml";

use "src/mts/interpm.sml";
use "src/mts/term/term.sml";
use "src/mts/term/pseudotype.sml";
use "src/mts/term/normalize.sml";
use "src/mts/check.sml";

fun compile () : unit =
  let
    val cvs : CharFileStream.stream = raise Fail ""
    val (r, s) = Tokenizer.run Tokenizer.tokenize cvs
  in
    (case r of
      Left (SOME tl) => raise Fail ""
    | Left NONE => raise Fail ""
    | Right e => PolyML.print e)
    (* (case tokenize cvs of
      ExcVal _ => raise Fail ""
    | ExcErr _ => raise Fail "") *)
    (*
    * load file
    * tokenize
    * parse
    * check
    *)
    (* SyntaxParser.getstate >>= (fn s =>
    SyntaxParser.putstate (TokenStream.fromList tl) >>
    SyntaxParser.modExpr () >>= (fn m =>
    MTSCheck.ptModexpr prog [] ([], [], []) >>= (fn m' =>
    return (raise Fail ""))))) *)
  end

fun main () =
  let
    fun exit _ = OS.Process.exit (OS.Process.success)
  in
    ()
  end

