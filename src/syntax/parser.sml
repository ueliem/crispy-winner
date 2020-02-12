structure TParser = ParserFunctor(Tokenizer.TokenStream)

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
  val primapp : unit -> Syntax.term TParser.Parser
  (* val declaration : unit -> Syntax.declaration TParser.Parser
  val program : unit -> Syntax.program TParser.Parser *)
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

  fun unitsymbol () = 
    satisfies (fn x => x = Tokenizer.UnitSymbol)

  fun lpar () = 
    satisfies (fn x => x = Tokenizer.LPar)

  fun rpar () = 
    satisfies (fn x => x = Tokenizer.RPar)

  fun lcurly () = 
    satisfies (fn x => x = Tokenizer.LCurly)

  fun rcurly () = 
    satisfies (fn x => x = Tokenizer.RCurly)

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

  fun regionannotation () =
    keyword (Tokenizer.At) >>= (fn _ =>
    ident () >>= (fn x =>
      return x
    ))

  fun regionset () =
    lcurly () >>= (fn _ =>
    optional (ident () >>= (fn r1 =>
    many (comma () >>= (fn _ =>
    ident () >>= (fn r =>
      return r
    ))) >>= (fn rl =>
      return (r1::rl)
    ))) >>= (fn rset =>
    rcurly () >>= (fn _ =>
      (case rset of
        SOME rs => return rs
      | NONE => return []
    ))))

  fun tyatom () = 
      tytuple ()
    ++ typaren ()
    ++ tyliteral ()
    ++ tyregabs ()
  and tytuple () =
    lpar () >>= (fn _ =>
    tyterm () >>= (fn x =>
    symbol Tokenizer.Star >>= (fn _ =>
    tyterm () >>= (fn y =>
    rpar () >>= (fn _ =>
    regionannotation () >>= (fn r =>
      return (Syntax.BoxedTy (Syntax.BoxTupleTy (x, y, r)))
    ))))))
  and typaren () = 
    lpar () >>= (fn _ =>
    tyterm () >>= (fn x =>
    rpar () >>= (fn _ =>
      return x
    )))
  and tyliteral () = 
    keyword (Tokenizer.KWInt) >>= (fn _ =>
    (keyword (Tokenizer.At) >>= (fn _ =>
    ident () >>= (fn r =>
      return (Syntax.BoxedTy (Syntax.BoxIntTy r))
    ))) ++ return Syntax.IntTy
    ) ++
    keyword (Tokenizer.KWBool) >>= (fn _ =>
    (keyword (Tokenizer.At) >>= (fn _ =>
    ident () >>= (fn r =>
      return (Syntax.BoxedTy (Syntax.BoxBoolTy r))
    ))) ++ return Syntax.BoolTy
    ) ++
    keyword (Tokenizer.KWUnit) >>= (fn _ =>
    (keyword (Tokenizer.At) >>= (fn _ =>
    ident () >>= (fn r =>
      return (Syntax.BoxedTy (Syntax.BoxUnitTy r))
    ))) ++ return Syntax.UnitTy
    )
  and tyregabs () =
    keyword (Tokenizer.ForAll) >>= (fn _ =>
    ident () >>= (fn r1 =>
    regionset () >>= (fn phi =>
    tyterm () >>= (fn t =>
    keyword (Tokenizer.At) >>= (fn _ =>
    ident () >>= (fn r2 =>
      return (Syntax.BoxedTy (Syntax.BoxRegFuncTy (r1, t, phi, r2)))
    ))))))

  and tyoperator () = 
    (symbol Tokenizer.Star >>= (fn _ => 
    ident () >>= (fn r => 
      return ("*", r, [])
    )))
    ++ (symbol Tokenizer.RightDashArrow >>= (fn _ => 
    ident ()>>= (fn r => 
    regionset () >>= (fn phi =>
      return ("->", r, phi)
    ))))
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
      tyoperator () >>= (fn (x, r, phi) =>
      (case retrieve x of
        SOME y => return ((x, r, phi), #2 y, #3 y)
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
          (fn (((b, r, phi), rhs), lhs) => 
            (case b of
              "->" => Syntax.BoxedTy (Syntax.BoxFuncTy (lhs, rhs, phi, r))
            | "*" => Syntax.BoxedTy (Syntax.BoxTupleTy (lhs, rhs, r))
            ))
          lhs brhsl)
    ))
  and tyterm () = typrec_parse 0

  fun atom () =
    parenterm ()
    ++ abstraction ()
    ++ ifelseterm ()
    ++ letterm ()
    ++ letregion ()
    ++ tuple ()
    ++ sel ()
    ++ regionelim ()
    ++ variable ()
    ++ literal () 

    (* TODO
    * unbox syntax
    *)
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
      return (Syntax.Var x)
    )
  and tuple () = 
    lpar () >>= (fn _ =>
    term () >>= (fn x =>
    comma () >>= (fn _ =>
    term () >>= (fn y =>
    rpar () >>= (fn _ =>
    regionannotation () >>= (fn r =>
      return (Syntax.BoxedValue (Syntax.BoxTuple (x, y, r)))
    ))))))
  and sel () = 
    keyword (Tokenizer.Select) >>= (fn _ =>
    integer () >>= (fn i =>
    term () >>= (fn x =>
      return (Syntax.Select (i, x))
    )))
  and regionelim () = 
    ident () >>= (fn f =>
    regionset () >>= (fn rs =>
    regionannotation () >>= (fn a =>
      (* TODO fix this because elim only eliminates one regionvar *)
      return (Syntax.RegionElim (f, hd rs, a))
    )))
  and literal () = 
    (integer () >>= (fn i =>
    optional (regionannotation ()) >>= (fn a =>
      (case a of
        SOME r => return (Syntax.BoxedValue (Syntax.BoxIntLit (i, r)))
      | NONE => return (Syntax.Value (Syntax.IntLit i))
    )))) ++ 
    (keyword (Tokenizer.True) >>= (fn _ =>
    optional (regionannotation ()) >>= (fn a =>
      (case a of
        SOME r => return (Syntax.BoxedValue (Syntax.BoxBoolLit (true, r)))
      | NONE => return (Syntax.Value (Syntax.BoolLit true))
    )))) ++
    (keyword (Tokenizer.False) >>= (fn _ =>
    optional (regionannotation ()) >>= (fn a =>
      (case a of
        SOME r => return (Syntax.BoxedValue (Syntax.BoxBoolLit (false, r)))
      | NONE => return (Syntax.Value (Syntax.BoolLit false))
    )))) ++
    (unitsymbol () >>= (fn _ =>
    optional (regionannotation ()) >>= (fn a =>
      (case a of
        SOME r => return (Syntax.BoxedValue (Syntax.BoxUnitLit r))
      | NONE => return (Syntax.Value (Syntax.UnitLit))
    ))))
  and application () =
    atom () >>= (fn x =>
    many (atom ()) >>= (fn apps =>
      return (foldl (fn (t, s) => Syntax.App (t, s)) x apps)
    ))
  and abstraction () =
    optional (keyword (Tokenizer.ForAll) >>= (fn _ => 
    ident () >>= (fn r =>
    regionset () >>= (fn rs => 
      return (r, rs)
    )))) >>= (fn regs =>
    keyword (Tokenizer.Fn) >>= (fn _ =>
    ident () >>= (fn x =>
    colon () >>= (fn _ =>
    tyterm () >>= (fn y =>
    rightarrow () >>= (fn _ =>
    term () >>= (fn e =>
    regionannotation () >>= (fn r2 =>
      (case regs of 
        SOME (r1, rs) =>
          return (Syntax.BoxedValue (Syntax.BoxAbs (foldl
            (fn (r, u) => Syntax.RegionLambda (r, u, r1))
            (Syntax.Lambda (x, e, y, r2))
            (List.rev rs))))
      | NONE => 
          return (Syntax.BoxedValue (Syntax.BoxAbs (Syntax.Lambda (x, e, y, r2))))
    )))))))))
  and ifelseterm () =
    keyword (Tokenizer.If) >>= (fn _ =>
    term () >>= (fn x =>
    keyword (Tokenizer.Then) >>= (fn _ =>
    term () >>= (fn y =>
    keyword (Tokenizer.Else) >>= (fn _ =>
    term () >>= (fn z =>
      return (Syntax.IfElse (x, y, z))
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
      return (Syntax.Let (x, y, z, t))
    )))))))))
  and letregion () =
    keyword (Tokenizer.LetRegion) >>= (fn _ =>
    ident () >>= (fn x =>
    keyword (Tokenizer.In) >>= (fn _ =>
    term () >>= (fn y =>
    keyword (Tokenizer.End) >>= (fn _ =>
      return (Syntax.LetRegion (x, y))
    )))))
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
          (fn ((b, rhs), lhs) => Syntax.PrimApp (b, lhs, rhs))
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

