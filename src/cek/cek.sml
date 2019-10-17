use "../../common/monad.sml";
use "lang.sml";
use "check.sml";
use "interp.sml";

open Lang
open Interp

val prog = App (Lambda ("x", Var "x", IntTy), IntLit 7)
(* val prog = Lambda ("x", Var "x", IntTy) *)

fun main () =
let
  val _ = PolyML.print_depth 100
  val _ = PolyML.print prog
  val initstate = (prog, EmptyEnv, Empty)
  val _ = PolyML.print initstate
  val _ = PolyML.print (TypeCheck.check [] prog { errs = [] })
  val _ = PolyML.print (runToCompletion initstate)
in
  ()
end

