structure SyntaxParser : sig
  include PARSER
  val binder : MTS.var monad
  val ptsLiteral : Syntax.term monad
  val ptsSort : Syntax.term monad
  val annotatedBinder : unit -> (MTS.var * Syntax.term) monad
  val binderList : unit -> (MTS.var * Syntax.term) list monad
  val path : unit -> Syntax.path monad
  val def : unit -> Syntax.def monad
  val specification : unit -> Syntax.specification monad
  val ptsTerm : unit -> Syntax.term monad
  val ptsPath : unit -> Syntax.term monad
  val ptsApp : unit -> Syntax.term monad
  val ptsCase : unit -> Syntax.term monad
  val ptsIfElse : unit -> Syntax.term monad
  val ptsLet : unit -> Syntax.term monad
  val ptsLambda : unit -> Syntax.term monad
  val ptsDepProduct : unit -> Syntax.term monad
  val modExpr : unit -> Syntax.modexpr monad
  val modStruct : unit -> Syntax.modexpr monad
  val modFunctor : unit -> Syntax.modexpr monad
  val modApp : unit -> Syntax.modexpr monad
  val modPath : unit -> Syntax.modexpr monad
  val modType : unit -> Syntax.modtype monad
  val modSig : unit -> Syntax.modtype monad
  val modFuncT : unit -> Syntax.modtype monad
  val parseTopLevel : Syntax.def list monad
  val parseStream : string -> unit monad
end = struct
  structure M = MTSCompilerM
  open MTSTokenParser
  open MTSTokenParserUtil

  val binder = (ident >>= (fn v => return (MTS.NamedVar v)))
    ++ (underscore >>= (fn _ => return (MTS.AnonVar)))
    ++ (throwHere [Err.Expected (Err.InfoMessage "binder")])
  val ptsLiteral = (kwInt >>= (fn _ => return (Syntax.Lit (MTS.IntTyLit))))
    ++ (kwBool >>= (fn _ => return (Syntax.Lit (MTS.BoolTyLit))))
    ++ (intLit >>= (fn i => return (Syntax.Lit (MTS.IntLit i))))
    ++ (boolLit >>= (fn b => return (Syntax.Lit (MTS.BoolLit b))))
    ++ (throwHere [Err.Expected (Err.InfoMessage "literal")])
  val ptsSort = (kwSet >>= (fn _ => return (Syntax.Sort (MTS.TypeVal))))
    ++ (kwType >>= (fn _ => return (Syntax.Sort (MTS.KindVal))))
    ++ (kwComp >>= (fn _ => return (Syntax.Sort (MTS.TypeComp))))
    ++ (kwTrans >>= (fn _ => return (Syntax.Sort (MTS.KindComp))))
    ++ (throwHere [Err.Expected (Err.InfoMessage "sort")])
  fun annotatedBinder () = lpar >>= (fn _ => binder >>= (fn v => colon >>= (fn _ =>
    ptsTerm () >>= (fn t => rpar >>= (fn _ => return (v, t))))))
  and binderList () = many1 (annotatedBinder ())
  and path () = (binder >>= (fn v =>
    many (period >>= (fn _ => binder)) >>= (fn vs =>
      return (v::vs))))
  and def _ =
    (kwVal >>= (fn _ => binder >>= (fn v =>
      (colon >>= (fn _ =>
        ptsTerm () >>= (fn t1 => defined >>= (fn _ => ptsTerm () >>= (fn t2 =>
          return (Syntax.DefTermTyped (v, t1, t2)))))))
      ++ (defined >>= (fn _ => ptsTerm () >>= (fn t =>
        return (Syntax.DefTerm (v, t))))))))
    ++ (kwModule >>= (fn _ => binder >>= (fn v =>
      (defined >>= (fn _ =>
        (kwTransparent >>= (fn _ => modExpr () >>= (fn m =>
          return (Syntax.DefModTransparent (v, m)))))
        ++ (modExpr () >>= (fn m => return (Syntax.DefMod (v, m))))))
      ++ (colon >>= (fn _ => modType () >>= (fn m2 =>
        (defined >>= (fn _ => modExpr () >>= (fn m1 =>
          return (Syntax.DefModSig (v, m1, m2)))))))))))
    ++ (inductive () >>= (fn (v, t, dcl) =>
      return (Syntax.DefInductive (v, t, dcl))))
    ++ (kwFixpoint >>= (fn _ => annotatedBinder () >>= (fn (v, t1) =>
      defined >>= (fn _ => ptsTerm () >>= (fn t2 =>
        return (Syntax.DefFixpoint (v, t1, t2)))))))
    ++ throwHere ([Err.Message "def"])
  and specification _ =
    (kwVal >>= (fn _ => binder >>= (fn v => colon >>= (fn _ =>
      ptsTerm () >>= (fn t1 =>
        (defined >>= (fn _ => ptsTerm () >>= (fn t2 =>
          return (Syntax.SpecManifestTerm (v, t1, t2)))))
        ++ (return (Syntax.SpecAbsTerm (v, t1))))))))
    ++ (kwModule >>= (fn _ => binder >>= (fn v => colon >>= (fn _ =>
      modType () >>= (fn m1 =>
        (defined >>= (fn _ => modExpr () >>= (fn m2 => 
            return (Syntax.SpecManifestMod (v, m1, m2)))))
        ++ (modType () >>= (fn m => return (Syntax.SpecAbsMod (v, m1)))))))))
    ++ (inductive () >>= (fn (v, t, dcl) =>
      return (Syntax.SpecInductive (v, t, dcl))))
    ++ throwHere ([Err.Message "spec"])
  and inductive () =
    (kwInductive >>= (fn _ => binder >>= (fn v =>
      colon >>= (fn _ => ptsTerm () >>= (fn t => defined >>= (fn _ =>
        many (pipe >>= (fn _ => binder >>= (fn v' =>
          colon >>= (fn _ => ptsTerm () >>= (fn t' =>
            return (v', t')))))) >>= (fn dcl =>
      kwEnd >>= (fn _ => return (v, t, dcl)))))))))
  and ptsAtom () =
    throwHere ([Err.Message "atom"])
    ++ ptsSort ++ ptsLiteral ++ ptsParen ()
    ++ ptsLet () ++ ptsLambda () ++ ptsDepProduct ()
    ++ ptsIfElse () ++ ptsCase () ++ ptsPath ()
  and ptsParen () =
    throwHere ([Err.Message "paren atom"])
    ++ (lpar >>= (fn _ => ptsTerm () >>= (fn t => rpar >>= (fn _ => return t))))
  and ptsTerm () =
    throwHere ([Err.Message "term"])
    ++ ptsApp () 
  and ptsPath () = (path () >>= (fn p => return (Syntax.Path p)))
    ++ throwHere ([Err.Message "pts path"])
  and ptsApp () =
    (many1 (ptsAtom ()) >>= (fn t =>
    if List.length t > 1 then 
      return (Syntax.App (List.hd t, List.tl t))
    else return (List.hd t)))
    ++ throwHere ([Err.Message "app"])
  and ptsCase () = let fun ptsAlt _ =
    path () >>= (fn c => many binder >>= (fn vs =>
    rightarrow >>= (fn _ => ptsTerm () >>= (fn t' => return (c, vs, t')))))
    in kwCase >>= (fn _ => ptsTerm () >>= (fn t1 => kwIn>>= (fn _ =>
      ptsTerm () >>= (fn t2 => kwOf >>= (fn _ =>
      many1 (pipe >>= (fn _ => ptsAlt ())) >>= (fn xs =>
      kwEnd >>= (fn _ => return (Syntax.Case (t1, t2, xs))))))))) end
  and ptsIfElse () = (kwIf >>= (fn _ => (ptsTerm () >>= (fn t1 =>
    kwThen >>= (fn _ => (ptsTerm () >>= (fn t2 =>
    kwElse >>= (fn _ => (ptsTerm () >>= (fn t3 =>
    return (Syntax.IfElse (t1, t2, t3))))))))))))
    ++ throwHere ([Err.Message "ifelse"])
  and ptsLet () = (kwLet >>= (fn _ => annotatedBinder () >>= (fn (v, t1) =>
    defined >>= (fn _ => ptsTerm () >>= (fn t2 =>
    kwIn >>= (fn _ => ptsTerm () >>= (fn t3 =>
    kwEnd >>= (fn _ => return (Syntax.Let (v, t1, t2, t3))))))))))
    ++ throwHere ([Err.Message "let"])
  and ptsLambda () = (kwFun >>= (fn _ => binderList () >>= (fn vtl =>
    rightarrow >>= (fn _ => ptsTerm () >>= (fn t2 =>
      return (Syntax.Lambda (vtl, t2)))))))
    ++ throwHere ([Err.Message "lambda"])
  and ptsDepProduct () = (kwForAll >>= (fn _ => annotatedBinder () >>= (fn (v, t1) =>
    rightarrow >>= (fn _ => ptsTerm () >>= (fn t2 =>
      return (Syntax.DepProduct ([(v, t1)], t2)))))))
    ++ throwHere ([Err.Message "forall"])
  and modExpr _ =
    modStruct () ++ modFunctor () ++ modApp () ++ modPath ()
    ++ throwHere ([Err.Message "mod expr"])
  and modStruct _ = kwStruct >>= (fn _ => many (def ()) >>= (fn vdl =>
    kwEnd >>= (fn _ => return (Syntax.ModStruct vdl))))
  and modFunctor _ = kwFunctor >>= (fn _ =>
    lpar >>= (fn _ => binder >>= (fn v => colon >>= (fn _ =>
      modType () >>= (fn m1 => rpar >>= (fn _ => rightarrow >>= (fn _ =>
      modExpr () >>= (fn m2 => return (Syntax.ModFunctor (v, m1, m2))))))))))
  and modApp _ = modExpr () >>= (fn m1 => modExpr () >>= (fn m2 =>
    return (Syntax.ModApp (m1, m2))))
  and modPath _ = path () >>= (fn p => return (Syntax.ModPath p))
  and modType _ =
    modSig () ++ modFuncT () (* ++ throwHere ([Err.Message "modtype"]) *)
  and modSig _ = kwSig >>= (fn _ => many (specification ()) >>= (fn vsl =>
    kwEnd >>= (fn _ => return (Syntax.ModTypeSig vsl))))
  and modFuncT _ = kwFuncT >>= (fn _ =>
    lpar >>= (fn _ => binder >>= (fn v => colon >>= (fn _ =>
      modType () >>= (fn m1 => rpar >>= (fn _ => rightarrow >>= (fn _ =>
      modType () >>= (fn m2 =>
        return (Syntax.ModTypeFunctor ([(v, m1)], m2))))))))))
  val parseTopLevel = (* throwHere ([Err.Message "on purpose"]) *)
    (def ()) >>= (fn tl => endOfInput >>= (fn _ => return [tl]))
  fun parseStream f =
    catch (getTokenStream f >>= (fn tvs =>
    putstate tvs >>= (fn _ =>
    parseTopLevel >>= (fn tl =>
    putSyntaxTree f tl >>= (fn _ =>
    return ())))), (fn (p, rs) =>
      printMsg (String.concat ["Errors at ", S.stringOfPos p, "\n"]) >>= (fn _ =>
      printMsg (Err.stringOfErrors rs))))
end

