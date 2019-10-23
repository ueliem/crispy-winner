use "common/monad.sml";
use "common/set.sml";
use "common/assoclist.sml";
use "parsercombinator/pc.sml";
use "parsercombinator/charparser.sml";
use "src/cek/lang.sml";
use "src/cek/check.sml";
use "src/cek/interp.sml";
use "src/cek/tokenizer.sml";
use "src/cek/parser.sml";

open Lang
open Interp

val prog = App (Value (Lambda ("x", Var "x", IntTy)), Value (IntLit 7))
(* val prog = Lambda ("x", Var "x", IntTy) *)
val seq = "fn x : int => x + 1"

fun main () =
let
  val _ = PolyML.print_depth 100
  val _ = PolyML.print prog
  val initstate = (prog, EmptyEnv, [], Empty)
  val _ = PolyML.print initstate
  val _ = PolyML.print (TypeCheck.check [] [] prog { errs = [] })
  val _ = PolyML.print (runToCompletion initstate)

  val contents : CharVector.vector = seq
  val _ = PolyML.print contents
  val t = Tokenizer.tokenize { pos = 0, s = contents }
  val _ = PolyML.print t
  val syn = SyntaxParser.term () t
  val _ = PolyML.print syn

  val _ = case syn of
    TParser.Ok (s, _) => 
    let
      val initstate1 = (s, EmptyEnv, [], Empty)
      val _ = PolyML.print initstate1
      val _ = PolyML.print (TypeCheck.check [] [] s { errs = [] })
      val _ = PolyML.print (runToCompletion initstate1)
    in
      ()
    end
  | _ => ()
in
  ()
end

