use "common/monad.sml";
use "parsercombinator/stream.sml";
use "parsercombinator/pc.sml";
use "src/mts/interpmt.sml";
use "src/mts/lang/mts.sml";
use "src/mts/lang/subst.sml";
use "src/mts/lang/alphaequiv.sml";
use "src/mts/interpm.sml";
use "src/mts/term/term.sml";
use "src/mts/term/pseudotype.sml";
use "src/mts/term/normalize.sml";
use "src/mts/check.sml";

fun main () =
  let
    val prog : MTS.modexpr = raise Fail ""
    val _ : unit = MTSCheck.ptModexpr
      prog
      []
      ([], [], [])
  in
    ()
  end

