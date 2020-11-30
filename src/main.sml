use "common/monad.sml";
use "parsercombinator/stream.sml";
use "parsercombinator/pc.sml";
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

open Tokenizer
open TokenizerUtil
open SyntaxParser
open TokenParserUtil

val compile =
  let
    val cvs : CharFileStream.stream = raise Fail ""
  in
    tokenize >>= (fn tl =>
    SyntaxParser.getstate >>= (fn s =>
    SyntaxParser.putstate (TokenStream.fromList tl) >>
    SyntaxParser.modExpr () >>= (fn m =>
    MTSCheck.ptModexpr prog [] ([], [], []) >>= (fn m' =>
    return (raise Fail "")))))
  end

fun main () =
  let
    val _ = raise Fail ""
  in
    ()
  end

