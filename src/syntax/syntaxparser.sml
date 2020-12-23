structure SyntaxParser : sig
  include PARSER
  structure M : MONAD
  structure TSP : PARSER
  val binder : Syntax.var monad
  val ptsLiteral : Syntax.term monad
  val ptsSort : Syntax.term monad
  val annotatedBinder : unit -> (Syntax.var * Syntax.term) monad
  val binderList : unit -> (Syntax.var * Syntax.term) list monad
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
end = struct
  structure M = MTSCompilerM
  structure TSP = MTSTokenParser
  open TSP
  open MTSTokenParserUtil
  val binder = (ident >>= (fn v => return (Syntax.NamedVar v)))
    ++ (underscore >> return (Syntax.AnonVar))
  val ptsLiteral = (kwInt >> return (Syntax.Lit (Syntax.IntTyLit)))
    ++ (kwBool >> return (Syntax.Lit (Syntax.BoolTyLit)))
    ++ (intLit >>= (fn i => return (Syntax.Lit (Syntax.IntLit i))))
    ++ (boolLit >>= (fn b => return (Syntax.Lit (Syntax.BoolLit b))))
  val ptsSort = (kwSet >> return (Syntax.Sort (Syntax.TypeVal)))
    ++ (kwType >> return (Syntax.Sort (Syntax.KindVal)))
    ++ (kwComp >> return (Syntax.Sort (Syntax.TypeComp)))
    ++ (kwTrans >> return (Syntax.Sort (Syntax.KindComp)))
  fun annotatedBinder () = lpar >> binder >>= (fn v => colon >>
    ptsTerm () >>= (fn t => rpar >> return (v, t)))
  and binderList () = many (annotatedBinder ())
  and path () = (binder >>= (fn v =>
    many (period >> binder) >>= (fn vs =>
      return (v::vs))))
  and def _ = (kwVal >> binder >>= (fn v => defined >>
    ptsTerm () >>= (fn t => return (Syntax.DefTerm (v, t)))))
    ++ (kwVal >> binder >>= (fn v => colon >>
      ptsTerm () >>= (fn t1 => defined >> ptsTerm () >>= (fn t2 =>
      return (Syntax.DefTermTyped (v, t1, t2))))))
    ++ (kwModule >> binder >>= (fn v => defined >>
      (kwTransparent >> modExpr () >>= (fn m =>
        return (Syntax.DefModTransparent (v, m))))
      ++ (modExpr () >>= (fn m1 => colon >> modType () >>= (fn m2 =>
        return (Syntax.DefModSig (v, m1, m2)))))
      ++ (modExpr () >>= (fn m => return (Syntax.DefMod (v, m))))))
    ++ (kwInductive >> binder >>= (fn v => colon >>
      ptsTerm () >>= (fn t => defined >>
      many (pipe >> binder >>= (fn v' =>
      colon >> ptsTerm () >>= (fn t' => return (v', t')))) >>= (fn dcl =>
      kwEnd >> return (Syntax.DefInductive (v, t, dcl))))))
    (* ++ (kwInductive >> binder >>= (fn v => colon >>
      ptsTerm () >>= (fn t => defined >>
      many (pipe >> binder >>= (fn v' =>
      colon >> ptsTerm () >>= (fn t' => return (v', t')))) >>= (fn dcl =>
      let val (vs, ts) = ListPair.unzip dcl in
        return ((v, Syntax.DefVal (Syntax.Inductive ((v, t), ts)))
          ::(List.tabulate (List.length dcl,
            (fn i => (List.nth (vs, i), Syntax.DefVal
              (Syntax.Constr (i, Syntax.Path (Syntax.PVar v))))))))end))))
              *)
  (* and specification _ =
    (ptsTerm () >>= (fn t => return (Syntax.SpecAbsTerm t)))
    ++ (ptsTerm () >>= (fn t1 => defined >> ptsTerm () >>= (fn t2 =>
      return (Syntax.SpecManifestTerm (t1, t2)))))
    ++ (modType () >>= (fn m => return (Syntax.SpecAbsMod m)))
    ++ (modType () >>= (fn m1 => defined >> modExpr () >>= (fn m2 =>
      return (Syntax.SpecManifestMod (m1, m2)))))
      *)
  and specification _ = (kwVal >> binder >>= (fn v => colon >>
    ptsTerm () >>= (fn t => return (Syntax.SpecAbsTerm (v, t)))))
    ++ (kwVal >> binder >>= (fn v => colon >>
      ptsTerm () >>= (fn t1 => defined >> ptsTerm () >>= (fn t2 =>
      return (Syntax.SpecManifestTerm (v, t1, t2))))))
    ++ (kwModule >> binder >>= (fn v => defined >>
      (modExpr () >>= (fn m1 => colon >> modType () >>= (fn m2 =>
        return (Syntax.SpecManifestMod (v, m2, m1)))))
      ++ (modType () >>= (fn m => return (Syntax.SpecAbsMod (v, m))))))
    ++ (kwInductive >> binder >>= (fn v => colon >>
      ptsTerm () >>= (fn t => defined >>
      many (pipe >> binder >>= (fn v' =>
      colon >> ptsTerm () >>= (fn t' => return (v', t')))) >>= (fn dcl =>
      kwEnd >> return (Syntax.SpecInductive (v, t, dcl))))))
  and ptsTerm () = ptsPath () ++ ptsLiteral ++ ptsSort
    ++ ptsApp () ++ ptsCase () ++ ptsIfElse ()
    ++ ptsLet () ++ ptsLambda () ++ ptsDepProduct ()
  and ptsPath () = path () >>= (fn p => return (Syntax.Path p))
  and ptsApp () = ptsTerm () >>= (fn t1 => ptsTerm () >>= (fn t2 =>
    return (Syntax.App (t1, t2))))
  and ptsCase () = let fun ptsAlt _ =
    binder >>= (fn c => many binder >>= (fn vs =>
    rightarrow >> ptsTerm () >>= (fn t' => return (c, vs, t'))))
    in kwCase >> ptsTerm () >>= (fn t => kwOf >>
      ptsAlt () >>= (fn x => many1 (pipe >> ptsAlt ()) >>= (fn xs =>
      (* return (Syntax.Case (t, x::xs)) *) raise Fail ""))) end
  and ptsIfElse () = kwIf >> ptsTerm () >>= (fn t1 =>
    kwThen >> ptsTerm () >>= (fn t2 =>
    kwElse >> ptsTerm () >>= (fn t3 =>
    return (Syntax.IfElse (t1, t2, t3)))))
  and ptsLet () = kwLet >> annotatedBinder () >>= (fn (v, t1) =>
    defined >> ptsTerm () >>= (fn t2 =>
    kwIn >> ptsTerm () >>= (fn t3 =>
    kwEnd >> return (Syntax.Let (v, t1, t2, t3)))))
  and ptsLambda () = kwFun >> binderList () >>= (fn vtl =>
    rightarrow >> ptsTerm () >>= (fn t2 =>
    return (Syntax.Lambda (vtl, t2))))
  and ptsDepProduct () = kwForAll >> annotatedBinder () >>= (fn (v, t1) =>
    rightarrow >> ptsTerm () >>= (fn t2 =>
    return (Syntax.DepProduct ([(v, t1)], t2))))
  and modExpr _ =
    modStruct () ++ modFunctor () ++ modApp () ++ modPath ()
  and modStruct _ = kwStruct >> many (def ()) >>= (fn vdl =>
    kwEnd >> return (Syntax.ModStruct vdl))
  and modFunctor _ = kwFunctor >> lpar >> binder >>= (fn v => colon >>
    modType () >>= (fn m1 => rpar >> rightarrow >>
    modExpr () >>= (fn m2 => return (Syntax.ModFunctor (v, m1, m2)))))
  and modApp _ = modExpr () >>= (fn m1 => modExpr () >>= (fn m2 =>
    return (Syntax.ModApp (m1, m2))))
  and modPath _ = path () >>= (fn p => return (Syntax.ModPath p))
  and modType _ = modSig () ++ modFuncT ()
  and modSig _ = kwSig >> many (specification ()) >>= (fn vsl =>
    kwEnd >> return (Syntax.ModTypeSig vsl))
  and modFuncT _ = kwFuncT >> lpar >> binder >>= (fn v => colon >>
    modType () >>= (fn m1 => rpar >> rightarrow >>
    modType () >>= (fn m2 =>
    return (Syntax.ModTypeFunctor ([(v, m1)], m2)))))
end

