(* use "common/common.sml";
use "common/monad.sml";
use "common/monadoption.sml";
use "common/monadstate.sml";
use "common/monadcont.sml";
use "common/monadreader.sml";
use "common/monadexception.sml";
use "src/compilerm.sml";
use "src/mts/interpmt.sml";
use "parsercombinator/stream.sml";
use "parsercombinator/pc.sml";
use "parsercombinator/charparser.sml";

use "src/mts/lang/mts.sml";
use "src/mts/lang/subst.sml";
use "src/mts/lang/alphaequiv.sml";
use "src/mtscompilerm.sml";

use "src/syntax/tokenizer.sml";
use "src/mtstoken.sml";
use "src/syntax/tokenparser.sml";
use "src/syntax/syntaxparser.sml";
*)
(*
use "src/mts/interpm.sml";
use "src/mts/term/term.sml";
use "src/mts/term/pseudotype.sml";
use "src/mts/term/normalize.sml";
use "src/mts/check.sml"; *)
(* use "src/compiler.sml"; *)

fun main () =
  let
    fun exit _ = OS.Process.exit (OS.Process.success)
    val _ = Compiler.compile ""
  in
    ()
  end

