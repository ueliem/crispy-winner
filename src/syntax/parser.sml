structure TErr = StreamError (structure S = Tokenizer.TokenStream)
structure TParser = ParserT (structure S = Tokenizer.TokenStream;
  structure E = TErr)

structure SyntaxParser : 
sig
  val any : Tokenizer.token TParser.Parser
  val satisfies : (Tokenizer.tok -> bool) -> Tokenizer.token TParser.Parser
  val keyword : Tokenizer.tok -> Tokenizer.token TParser.Parser
  val eoi : unit -> Tokenizer.token TParser.Parser
  val atom : unit -> Term.term TParser.Parser
  val term : unit -> Term.term TParser.Parser
  val variable : unit -> Term.term TParser.Parser
  val literal : unit -> Term.term TParser.Parser
  val application : unit -> Term.term TParser.Parser
  val abstraction : unit -> Term.term TParser.Parser
  val primapp : unit -> Term.term TParser.Parser
  val declaration : unit -> Program.declaration TParser.Parser
  val program : unit -> Program.program TParser.Parser
end
=
struct
  open TParser

  datatype assoc =
    RightAssoc
  | LeftAssoc
  | NoAssoc

  val any =
    (fn (s : Tokenizer.TokenStream.stream) =>
      (case Tokenizer.TokenStream.uncons s of
        SOME (x, xs) => (TParser.Ok (x), xs)
      | NONE => (Error (TErr.empty (~1, ~1)), s)))

  fun satisfies f = 
    any >>= (fn x =>
    if f (#2 x) then return x else unexpected (x))

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
    | _ => false) >>= (fn x => case x of (_, Tokenizer.Identifier i) => return i
    | _ => raise Fail "not an identifier")

  fun integer () =
    satisfies (fn x => case x of Tokenizer.Integer _ => true
    | _ => false) >>= (fn x => case x of (_, Tokenizer.Integer i) => return i
    | _ => raise Fail "not an integer ")

  fun regionannotation () =
    keyword (Tokenizer.At) >>= (fn _ =>
    ident () >>= (fn x =>
      return x
    ))

  fun regionset () =
    (lcurly () >>= (fn _ =>
    rcurly () >>= (fn _ =>
      return [])))
    ++
    ((lcurly () >>= (fn _ =>
    ident () >>= (fn r1 =>
    many (comma () >>= (fn _ =>
    ident () >>= (fn r =>
      return r
    ))) >>= (fn rl =>
      return (r1::rl)
    )))) >>= (fn rset =>
    rcurly () >>= (fn _ =>
      return rset
    )))

  fun tyterm () = 
      tytuple ()
    ++ typaren ()
    ++ tyliteral ()
    ++ tyfun ()
  and tyfun () = 
    keyword (Tokenizer.ForAll) >>= (fn _ =>
    regionset () >>= (fn rvl =>
    lpar () >>= (fn _ =>
    tyterm () >>= (fn x =>
    many (comma () >>= (fn _ =>
    tyterm () >>= (fn r =>
      return r
    ))) >>= (fn rl =>
    rpar () >>= (fn _ =>
    symbol Tokenizer.RightDashArrow >>= (fn _ => 
    regionset () >>= (fn phi => 
    tyterm () >>= (fn y =>
      return (Ty.FuncTy (Set.fromList rvl, x::rl, y, Set.fromList phi))
    )))))))))
  and tytuple () =
    lpar () >>= (fn _ =>
    tyterm () >>= (fn x =>
    many1 (symbol Tokenizer.Star >>= (fn _ =>
    tyterm () >>= (fn y =>
      return y
    ))) >>= (fn z =>
    rpar () >>= (fn _ =>
    regionannotation () >>= (fn r =>
      return (Ty.TupleTy (x::z))
    )))))
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
      return (Ty.BoxedTy (Ty.IntTy, r))
    ))) ++ return Ty.IntTy
    ) ++
    keyword (Tokenizer.KWBool) >>= (fn _ =>
    (keyword (Tokenizer.At) >>= (fn _ =>
    ident () >>= (fn r =>
      return (Ty.BoxedTy (Ty.BoolTy, r))
    ))) ++ return Ty.BoolTy
    ) ++
    keyword (Tokenizer.KWUnit) >>= (fn _ =>
    (keyword (Tokenizer.At) >>= (fn _ =>
    ident () >>= (fn r =>
      return (Ty.BoxedTy (Ty.UnitTy, r))
    ))) ++ return Ty.UnitTy
    )

  fun atom () =
    parenterm ()
    ++ abstraction ()
    ++ ifelseterm ()
    ++ letterm ()
    ++ letregion ()
    ++ tuple ()
    ++ unbox ()
    ++ sel ()
    ++ regionelim ()
    ++ variable ()
    ++ literal () 
  and term () =
    (primapp ()
    ++ application ()
    ++ atom ()) >>= (fn m =>
    optional (regionannotation ()) >>= (fn a =>
      (case a of
        SOME r => return (Term.Box (m, r))
      | NONE => return m
    )))
  and parenterm () = 
    lpar () >>= (fn _ =>
    term () >>= (fn x =>
    rpar () >>= (fn _ =>
      return x
    )))
  and variable () = 
    ident () >>= (fn x =>
      return (Term.Var x)
    )
  and tuple () = 
    lpar () >>= (fn _ =>
    term () >>= (fn x =>
    many1 (comma () >>= (fn _ =>
    term () >>= (fn y =>
      return y
    ))) >>= (fn z =>
    rpar () >>= (fn _ =>
      return (Term.Value (Term.Tuple (x::z)))
    ))))
  and unbox () = 
    keyword (Tokenizer.KWUnbox) >>= (fn _ =>
    term () >>= (fn x =>
      return (Term.Unbox x)
    ))
  and sel () = 
    keyword (Tokenizer.Select) >>= (fn _ =>
    integer () >>= (fn i =>
    term () >>= (fn x =>
      return (Term.Select (i, x))
    )))
  and regionelim () = 
    keyword (Tokenizer.KWElim) >>= (fn _ =>
    regionset () >>= (fn rs =>
    term () >>= (fn x =>
      return (Term.RegionElim (Set.fromList rs, x))
    )))
  and literal () = 
    (integer () >>= (fn i =>
      return (Term.Value (Term.IntLit i))
    )) ++ 
    (keyword (Tokenizer.True) >>= (fn _ =>
      return (Term.Value (Term.BoolLit true))
    )) ++
    (keyword (Tokenizer.False) >>= (fn _ =>
      return (Term.Value (Term.BoolLit false))
    )) ++
    (unitsymbol () >>= (fn _ =>
      return (Term.Value (Term.UnitLit))
    ))
  and application () =
    atom () >>= (fn x =>
    many1 (atom ()) >>= (fn apps =>
      return (Term.App (x, apps))
    ))
  and abstraction () =
    keyword (Tokenizer.Fn) >>= (fn _ =>
    regionset () >>= (fn rs =>
    many1 (lpar () >>= (fn _ => 
    ident () >>= (fn x =>
    colon () >>= (fn _ =>
    tyterm () >>= (fn y =>
    rpar () >>= (fn _ =>
      return (x, y)
    )))))) >>= (fn z =>
    colon () >>= (fn _ =>
    regionset () >>= (fn eff =>
    tyterm () >>= (fn returnt =>
    rightarrow () >>= (fn _ =>
    term () >>= (fn e =>
      let val (x, y) = ListPair.unzip z
      in
        return (Term.Value (
          Term.Lambda (Set.fromList rs, z, returnt, Set.fromList eff, e)))
      end
    ))))))))
  and ifelseterm () =
    keyword (Tokenizer.If) >>= (fn _ =>
    term () >>= (fn x =>
    keyword (Tokenizer.Then) >>= (fn _ =>
    term () >>= (fn y =>
    keyword (Tokenizer.Else) >>= (fn _ =>
    term () >>= (fn z =>
      return (Term.IfElse (x, y, z))
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
      return (Term.Let (x, y, z, t))
    )))))))))
  and letregion () =
    keyword (Tokenizer.LetRegion) >>= (fn _ =>
    ident () >>= (fn x =>
    keyword (Tokenizer.In) >>= (fn _ =>
    term () >>= (fn y =>
    keyword (Tokenizer.End) >>= (fn _ =>
      return (Term.LetRegion (x, y))
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
      | NONE => fail ()))
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
          (fn ((b, rhs), lhs) => Term.PrimApp (b, [lhs, rhs]))
          lhs brhsl)
    ))

  fun tydeclaration () =
    keyword (Tokenizer.KWType) >>= (fn _ =>
    ident () >>= (fn x =>
    equal () >>= (fn _ =>
    tyterm () >>= (fn y =>
      return (Program.DeclType (x, y))
    ))))

  fun valdeclaration () =
    keyword (Tokenizer.Val) >>= (fn _ =>
    ident () >>= (fn x =>
    colon () >>= (fn _ =>
    tyterm () >>= (fn t =>
    equal () >>= (fn _ =>
    term () >>= (fn y =>
      return (Program.DeclVal (x, t, y))
    ))))))

  fun fundeclaration () =
    keyword (Tokenizer.Fun) >>= (fn _ =>
    ident () >>= (fn f =>
    many1 (lpar () >>= (fn _ =>
    ident () >>= (fn x =>
    colon () >>= (fn _ =>
    tyterm () >>= (fn s =>
    rpar () >>= (fn _ =>
      return (x, s)
    )))))) >>= (fn xs =>
    colon () >>= (fn _ =>
    tyterm () >>= (fn returnt =>
    equal () >>= (fn _ =>
    term () >>= (fn z =>
      let val (x, argt) = ListPair.unzip xs
      in
        return (Program.DeclFun (f, x, argt, returnt, z))
      end
    )))))))

  fun declaration () =
      tydeclaration ()
    ++ valdeclaration ()
    ++ fundeclaration ()

  fun program () =
    many1 (declaration ()) >>= (fn d =>
    eoi () >>= (fn _ =>
      return (Program.Prog d)
    ))

end

