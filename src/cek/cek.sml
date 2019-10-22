use "../../common/monad.sml";
use "../../common/set.sml";
use "lang.sml";
use "check.sml";
use "interp.sml";

open Lang
open Interp

val prog = App (Value (Lambda ("x", Var "x", IntTy)), Value (IntLit 7))
(* val prog = Lambda ("x", Var "x", IntTy) *)

fun main () =
let
  val _ = PolyML.print_depth 100
  val _ = PolyML.print prog
  val initstate = (prog, EmptyEnv, [], Empty)
  val _ = PolyML.print initstate
  val _ = PolyML.print (TypeCheck.check [] [] prog { errs = [] })
  val _ = PolyML.print (runToCompletion initstate)
in
  ()
end

