structure TParser = ParserFunctor(Tokenizer.TokenStream)

structure SyntaxParser : 
sig
  val satisfies : (Tokenizer.token -> bool) -> Tokenizer.token TParser.Parser
  val keyword : Tokenizer.token -> Tokenizer.token TParser.Parser
  val eoi : unit -> Tokenizer.token TParser.Parser
  val atom : unit -> Lang.term TParser.Parser
  val term : unit -> Lang.term TParser.Parser
  val variable : unit -> Lang.term TParser.Parser
  val literal : unit -> Lang.term TParser.Parser
  val application : unit -> Lang.term TParser.Parser
  val abstraction : unit -> Lang.term TParser.Parser
  val primapp : unit -> Lang.term TParser.Parser
  (* val declaration : unit -> Lang.declaration TParser.Parser
  val program : unit -> Lang.program TParser.Parser *)
end
=
struct
  open TParser

  datatype assoc =
    RightAssoc
  | LeftAssoc
  | NoAssoc

  fun any () =
    (fn (s : Tokenizer.TokenStream.stream) =>
      (case Tokenizer.TokenStream.uncons s of
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

  fun tyatom () = 
    typaren ()
    ++ tyliteral ()
  and typaren () = 
    lpar () >>= (fn _ =>
    tyterm () >>= (fn x =>
    rpar () >>= (fn _ =>
      return x
    )))
  and tyliteral () = 
    keyword (Tokenizer.KWInt) >>= (fn _ =>
      return Lang.IntTy
    ) ++
    keyword (Tokenizer.KWBool) >>= (fn _ =>
      return Lang.BoolTy
    )
  and tyoperator () = 
    symbol Tokenizer.Star >>= (fn x => return "*")
    ++ symbol Tokenizer.RightDashArrow >>= (fn x => return "->")
  and tybinop level =
    let 
      val opr = [
      ("->", 4, LeftAssoc),
      ("*", 7, LeftAssoc)
      ]
      fun retrieve x = 
        case List.find (fn y => #1 y = x) opr of
          SOME z => if #2 z >= level then SOME z else NONE
        | NONE => NONE (* raise Fail ("Not an operator: " ^ x) *)
    in
      tyoperator () >>= (fn x =>
      (case retrieve x of
        SOME y => return y
      | NONE => fail))
    end
  and typrec_helper level =
    tybinop level >>= (fn (b, p, a) =>
    typrec_parse (case a of LeftAssoc => (p + 1) | _ => p) >>= (fn rhs =>
      return (b, rhs)
    ))
  and typrec_parse level = 
    tyatom () >>= (fn lhs =>
    many (typrec_helper level) >>= (fn brhsl =>
      return
        (foldl 
          (fn ((b, rhs), lhs) => Lang.TupleTy (lhs, rhs))
          lhs brhsl)
    ))
  and tyterm () = typrec_parse 0

  fun atom () =
    parenterm ()
    ++ abstraction ()
    ++ letterm ()
    ++ pair ()
    ++ fst ()
    ++ snd ()
    ++ variable ()
    ++ literal () 
  and term () =
    primapp ()
    ++ application ()
    ++ atom ()
  and parenterm () = 
    lpar () >>= (fn _ =>
    term () >>= (fn x =>
    rpar () >>= (fn _ =>
      return x
    )))
  and variable () = 
    ident () >>= (fn x =>
      return (Lang.Var x)
    )
  and pair () = 
    lpar () >>= (fn _ =>
    term () >>= (fn x =>
    comma () >>= (fn _ =>
    term () >>= (fn y =>
    rpar () >>= (fn _ =>
      return (Lang.Value (Lang.Tuple (x, y)))
    )))))
  and fst () = 
    keyword (Tokenizer.First) >>= (fn _ =>
    term () >>= (fn x =>
      return (Lang.First x)
    ))
  and snd () = 
    keyword (Tokenizer.Second) >>= (fn _ =>
    term () >>= (fn x =>
      return (Lang.Second x)
    ))
  and literal () = 
    integer () >>= (fn i =>
      return (Lang.Value (Lang.IntLit i))
    ) ++
    keyword (Tokenizer.True) >>= (fn _ =>
      return (Lang.Value (Lang.BoolLit true))
    ) ++
    keyword (Tokenizer.False) >>= (fn _ =>
      return (Lang.Value (Lang.BoolLit false))
    )
  and application () =
    atom () >>= (fn x =>
    many (atom ()) >>= (fn apps =>
      return (foldl (fn (t, s) => Lang.App (t, s)) x apps)
    ))
  and abstraction () =
    keyword (Tokenizer.Fn) >>= (fn _ =>
    ident () >>= (fn x =>
    colon () >>= (fn _ =>
    tyterm () >>= (fn y =>
    rightarrow () >>= (fn _ =>
    term () >>= (fn e =>
      return (Lang.Value (Lang.Lambda (x, e, y)))
    ))))))
  and letterm () =
    keyword (Tokenizer.Let) >>= (fn _ =>
    ident () >>= (fn x =>
    colon () >>= (fn _ =>
    tyterm () >>= (fn t =>
    equal () >>= (fn _ =>
    term () >>= (fn y =>
    keyword (Tokenizer.In) >>= (fn _ =>
    term () >>= (fn z =>
    keyword (Tokenizer.End) >>= (fn _ =>
      return (Lang.Let (x, y, z, t))
    )))))))))
  and primapp () = prec_parse 0
  and operator () =
    symbol Tokenizer.Plus >>= (fn x => return "+")
    ++ symbol Tokenizer.Dash >>= (fn x => return "-")
    ++ symbol Tokenizer.Star >>= (fn x => return "*")
    ++ symbol Tokenizer.Slash >>= (fn x => return "/")
    ++ symbol Tokenizer.EqualEqual >>= (fn x => return "==")
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
      ("==", 4, LeftAssoc),
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
      return
        (foldl 
          (fn ((b, rhs), lhs) => Lang.PrimApp (b, Lang.Value (Lang.Tuple (lhs, rhs))))
          lhs brhsl)
    ))

  (* fun declaration () =
    keyword (Tokenizer.Val) >>= (fn _ =>
    ident () >>= (fn x =>
    colon () >>= (fn _ =>
    term () >>= (fn y =>
    equal () >>= (fn _ =>
    primapp () >>= (fn z =>
      return (Syntax.Value (Syntax.Var x, y, z))
    ))))))

  fun program () =
    many1 (declaration ()) >>= (fn d =>
    eoi () >>= (fn _ =>
      return (Syntax.Prog d)
    )) *)

end

