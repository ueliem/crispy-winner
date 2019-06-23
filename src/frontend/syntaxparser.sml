structure TParser = ParserFunctor(type item = Tokenizer.token)

structure SyntaxParser : 
sig
  val satisfies : (Tokenizer.token -> bool) -> Tokenizer.token TParser.Parser
  val keyword : Tokenizer.token -> Tokenizer.token TParser.Parser
  val eoi : unit -> Tokenizer.token TParser.Parser
  val atom : unit -> Syntax.term TParser.Parser
  val term : unit -> Syntax.term TParser.Parser
  val variable : unit -> Syntax.term TParser.Parser
  val literal : unit -> Syntax.term TParser.Parser
  val application : unit -> Syntax.term TParser.Parser
  val abstraction : unit -> Syntax.term TParser.Parser
  val program : unit -> Syntax.program TParser.Parser
end
=
struct
  open TParser

  datatype assoc =
    RightAssoc
  | LeftAssoc
  | NoAssoc

  fun any () =
    (fn (s : Tokenizer.token Stream.stream) =>
      (case Stream.uncons s of
        SOME (x, xs) => TParser.Ok (x, xs)
      | NONE => fail s))

  fun satisfies f = 
    any () >>= (fn x =>
    if f x then return x else fail)

  fun keyword k =
    satisfies (fn x => x = k)

  fun symbol k =
    satisfies (fn x => x = k)
    
  fun eoi () =
    satisfies (fn x => x = Tokenizer.EOI)

  fun lpar () = 
    satisfies (fn x => x = Tokenizer.LPar)

  fun rpar () = 
    satisfies (fn x => x = Tokenizer.RPar)

  fun rightarrow () = 
    satisfies (fn x => x = Tokenizer.RightArrow)

  fun rightdasharrow () = 
    satisfies (fn x => x = Tokenizer.RightDashArrow)

  fun equal () = 
    satisfies (fn x => x = Tokenizer.Equal)

  fun colon () = 
    satisfies (fn x => x = Tokenizer.Colon)

  fun comma () = 
    satisfies (fn x => x = Tokenizer.Comma)

  fun ident () =
    satisfies (fn x => case x of Tokenizer.Identifier _ => true
    | _ => false) >>= (fn x => case x of Tokenizer.Identifier i => return i
    | _ => raise Fail "not an identifier")

  fun integer () =
    satisfies (fn x => case x of Tokenizer.Integer _ => true
    | _ => false) >>= (fn x => case x of Tokenizer.Integer i => return i
    | _ => raise Fail "not an integer ")

  fun atom () =
    parenterm ()
    ++ abstraction ()
    ++ depprod ()
    ++ depsum ()
    ++ letterm ()
    ++ pair ()
    ++ fst ()
    ++ snd ()
    ++ variable ()
    ++ literal () 
  and term () =
    application ()
    ++ primapp ()
    ++ atom ()
  and parenterm () = 
    lpar () >>= (fn _ =>
    term () >>= (fn x =>
    rpar () >>= (fn _ =>
      return x
    )))
  and variable () = 
    ident () >>= (fn x =>
    colon () >>= (fn _ =>
    term () >>= (fn y =>
      return (Syntax.Variable (Syntax.Var x, y))
    )))
  and pair () = 
    lpar () >>= (fn _ =>
    term () >>= (fn x =>
    comma () >>= (fn _ =>
    term () >>= (fn y =>
    rpar () >>= (fn _ =>
      return (Syntax.Pair (x, y))
    )))))
  and fst () = 
    keyword (Tokenizer.First) >>= (fn _ =>
    term () >>= (fn x =>
      return (Syntax.Fst x)
    ))
  and snd () = 
    keyword (Tokenizer.Second) >>= (fn _ =>
    term () >>= (fn x =>
      return (Syntax.Snd x)
    ))
  and literal () = 
    integer () >>= (fn i =>
      return (Syntax.Literal (Syntax.IntLit i))
    ) ++
    keyword (Tokenizer.KWInt) >>= (fn _ =>
      return (Syntax.Literal (Syntax.IntType))
    ) ++
    keyword (Tokenizer.KWBool) >>= (fn _ =>
      return (Syntax.Literal (Syntax.BoolType))
    ) ++
    keyword (Tokenizer.True) >>= (fn _ =>
      return (Syntax.Literal (Syntax.BoolLit true))
    ) ++
    keyword (Tokenizer.False) >>= (fn _ =>
      return (Syntax.Literal (Syntax.BoolLit false))
    )
  and application () =
    atom () >>= (fn x =>
    many (atom ()) >>= (fn apps =>
      return (foldl (fn (t, s) => Syntax.App (t, s)) x apps)
    ))
  and abstraction () =
    keyword (Tokenizer.Fn) >>= (fn _ =>
    ident () >>= (fn x =>
    colon () >>= (fn _ =>
    term () >>= (fn y =>
    rightarrow () >>= (fn _ =>
    term () >>= (fn e =>
      return (Syntax.Abs (Syntax.Var x, y, e))
    ))))))
  and depprod () =
    keyword (Tokenizer.Pi) >>= (fn _ =>
    ident () >>= (fn x =>
    colon () >>= (fn _ =>
    term () >>= (fn y =>
    rightarrow () >>= (fn _ =>
    term () >>= (fn e =>
      return (Syntax.DepProd (Syntax.Var x, y, e))
    ))))))
  and depsum () =
    keyword (Tokenizer.Sigma) >>= (fn _ =>
    ident () >>= (fn x =>
    colon () >>= (fn _ =>
    term () >>= (fn y =>
    rightarrow () >>= (fn _ =>
    term () >>= (fn e =>
      return (Syntax.DepSum (Syntax.Var x, y, e))
    ))))))
  and letterm () =
    keyword (Tokenizer.Let) >>= (fn _ =>
    ident () >>= (fn x =>
    colon () >>= (fn _ =>
    term () >>= (fn y =>
    equal () >>= (fn _ =>
    term () >>= (fn z =>
    keyword (Tokenizer.In) >>= (fn _ =>
    term () >>= (fn w =>
    keyword (Tokenizer.End) >>= (fn _ =>
      return (Syntax.LetTerm (Syntax.Var x, y, z, w))
    )))))))))
  and primapp () = prec_parse 0
  and operator () =
    symbol Tokenizer.Plus >>= (fn x => return "+")
    ++ symbol Tokenizer.Dash >>= (fn x => return "-")
    ++ symbol Tokenizer.Star >>= (fn x => return "*")
    ++ symbol Tokenizer.Slash >>= (fn x => return "/")
    ++ symbol Tokenizer.Equal >>= (fn x => return "=")
    ++ symbol Tokenizer.NotEqual >>= (fn x => return "<>")
    ++ symbol Tokenizer.Less >>= (fn x => return "<")
    ++ symbol Tokenizer.Greater >>= (fn x => return ">")
    ++ symbol Tokenizer.LessEq >>= (fn x => return "<=")
    ++ symbol Tokenizer.GreaterEq >>= (fn x => return ">=")
    ++ symbol Tokenizer.RightDashArrow >>= (fn x => return "->")
  and binop level =
    let 
      val opr = [
      ("->", 4, LeftAssoc),
      ("=", 4, LeftAssoc),
      ("<>", 4, LeftAssoc),
      ("<", 4, LeftAssoc),
      (">", 4, LeftAssoc),
      ("<=", 4, LeftAssoc),
      (">=", 4, LeftAssoc),
      ("+", 6, LeftAssoc),
      ("-", 6, LeftAssoc),
      ("*", 7, LeftAssoc),
      ("/", 7, LeftAssoc)
      ]
      fun retrieve x = 
        case List.find (fn y => #1 y = x) opr of
          SOME z => if #2 z >= level then SOME z else NONE
        | NONE => NONE (* raise Fail ("Not an operator: " ^ x) *)
    in
      operator () >>= (fn x =>
      (case retrieve x of
        SOME y => return y
      | NONE => fail))
    end
  and prec_helper level =
    binop level >>= (fn (b, p, a) =>
    prec_parse (case a of LeftAssoc => (p + 1) | _ => p) >>= (fn rhs =>
      return (b, rhs)
    ))
  and prec_parse level =
    atom () >>= (fn lhs =>
    many (prec_helper level) >>= (fn brhsl =>
      return (foldl (fn ((b, rhs), lhs) => Syntax.PrimApp (b, lhs, rhs)) lhs brhsl)
    ))

  fun declaration () =
    keyword (Tokenizer.Val) >>= (fn _ =>
    ident () >>= (fn x =>
    colon () >>= (fn _ =>
    term () >>= (fn y =>
    equal () >>= (fn _ =>
    term () >>= (fn z =>
      return (Syntax.Value (Syntax.Var x, y, z))
    ))))))

  fun program () =
    many1 (declaration ()) >>= (fn d =>
    eoi () >>= (fn _ =>
      return (Syntax.Prog d)
    ))

end

