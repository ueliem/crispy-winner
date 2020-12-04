structure SyntaxParser : sig
  include PARSER
  val binder : MTS.var monad
  val annotatedBinder : unit -> (MTS.var * MTS.term) monad
  val path : unit -> MTS.path monad
  val def : unit -> MTS.def monad
  val specification : unit -> MTS.specification monad
  val ptsTerm : unit -> MTS.term monad
  val ptsPath : unit -> MTS.term monad
  val ptsLiteral : unit -> MTS.term monad
  val ptsSort : unit -> MTS.term monad
  val ptsApp : unit -> MTS.term monad
  val ptsCase : unit -> MTS.term monad
  val ptsIfElse : unit -> MTS.term monad
  val ptsLet : unit -> MTS.term monad
  val ptsLambda : unit -> MTS.term monad
  val ptsDepProduct : unit -> MTS.term monad
  val modExpr : unit -> MTS.modexpr monad
  val modStruct : unit -> MTS.modexpr monad
  val modFunctor : unit -> MTS.modexpr monad
  val modApp : unit -> MTS.modexpr monad
  val modPath : unit -> MTS.modexpr monad
  val modType : unit -> MTS.modtype monad
  val modSig : unit -> MTS.modtype monad
  val modFuncT : unit -> MTS.modtype monad
end = struct
  open TokenParser
  open TokenParserUtil
  val binder = (ident >>= (fn v => return (MTS.NamedVar v)))
    ++ (underscore >> return (MTS.AnonVar))
  fun annotatedBinder _ = lpar >> binder >>= (fn v => colon >>
    ptsTerm () >>= (fn t => rpar >> return (v, t)))
  and path _ = (binder >>= (fn v => return (MTS.PVar v)))
    ++ (modExpr () >>= (fn m => period >> binder >>= (fn v =>
      return (MTS.PPath (m, v)))))
  and def _ = (ptsTerm () >>= (fn t => return (MTS.DefVal t)))
  ++ (kwInductive >> colon >> ptsTerm () >>= (fn t =>
    defined >> many (binder >>= (fn v' =>
    colon >> ptsTerm () >>= (fn t' => semicolon >>
    return ((v', v'), t')))) >>= (fn vtl =>
    return (MTS.DefData (t, vtl)))))
  ++ (modExpr () >>= (fn m => return (MTS.DefMod m)))
  ++ (modExpr () >>= (fn m1 => colon >> modType () >>= (fn m2 =>
    return (MTS.DefModSig (m1, m2)))))
  ++ (kwTransparent >> modExpr () >>= (fn m =>
    return (MTS.DefModTransparent m)))
  and specification _ =
    (ptsTerm () >>= (fn t => return (MTS.SpecAbsTerm t)))
    ++ (ptsTerm () >>= (fn t1 => defined >> ptsTerm () >>= (fn t2 =>
      return (MTS.SpecManifestTerm (t1, t2)))))
    ++ (modType () >>= (fn m => return (MTS.SpecAbsMod m)))
    ++ (modType () >>= (fn m1 => defined >> modExpr () >>= (fn m2 =>
      return (MTS.SpecManifestMod (m1, m2)))))
  and ptsTerm _ = ptsPath () ++ ptsLiteral () ++ ptsSort ()
    ++ ptsApp () ++ ptsCase () ++ ptsIfElse ()
    ++ ptsLet () ++ ptsLambda () ++ ptsDepProduct ()
  and ptsPath _ = path () >>= (fn p => return (MTS.Path p))
  and ptsLiteral _ = (kwInt >> return (MTS.Lit (MTS.IntTyLit)))
    ++ (kwBool >> return (MTS.Lit (MTS.BoolTyLit)))
    ++ (intLit >>= (fn i => return (MTS.Lit (MTS.IntLit i))))
    ++ (boolLit >>= (fn b => return (MTS.Lit (MTS.BoolLit b))))
  and ptsSort _ = (kwSet >> return (MTS.Sort (MTS.TypeVal)))
    ++ (kwType >> return (MTS.Sort (MTS.KindVal)))
    ++ (kwComp >> return (MTS.Sort (MTS.TypeComp)))
    ++ (kwTrans >> return (MTS.Sort (MTS.KindComp)))
  and ptsApp _ = ptsTerm () >>= (fn t1 => ptsTerm () >>= (fn t2 =>
    return (MTS.App (t1, t2))))
  and ptsCase _ = let fun ptsAlt _ =
    binder >>= (fn c => many binder >>= (fn vs =>
    rightarrow >> ptsTerm () >>= (fn t' => return (c, vs, t'))))
    in kwCase >> ptsTerm () >>= (fn t => kwOf >>
      ptsAlt () >>= (fn x => many1 (pipe >> ptsAlt ()) >>= (fn xs =>
      return (MTS.Case (t, x::xs))))) end
  and ptsIfElse _ = kwIf >> ptsTerm () >>= (fn t1 =>
    kwThen >> ptsTerm () >>= (fn t2 =>
    kwElse >> ptsTerm () >>= (fn t3 =>
    return (MTS.IfElse (t1, t2, t3)))))
  and ptsLet _ = kwLet >> annotatedBinder () >>= (fn (v, t1) =>
    defined >> ptsTerm () >>= (fn t2 =>
    kwIn >> ptsTerm () >>= (fn t3 =>
    kwEnd >> return (MTS.Let (v, t1, t2, t3)))))
  and ptsLambda _ = kwFun >> annotatedBinder () >>= (fn (v, t1) =>
    rightarrow >> ptsTerm () >>= (fn t2 =>
    return (MTS.Lambda (v, t1, t2))))
  and ptsDepProduct _ = kwForAll >> annotatedBinder () >>= (fn (v, t1) =>
    rightarrow >> ptsTerm () >>= (fn t2 =>
    return (MTS.DepProduct (v, t1, t2))))
  and modExpr _ =
    modStruct () ++ modFunctor () ++ modApp () ++ modPath ()
  and modStruct _ = kwStruct >> many (binder >>= (fn v =>
    defined >> def () >>= (fn d => semicolon >>
    return ((v, v), d)))) >>= (fn vdl => return (MTS.ModStruct vdl))
  and modFunctor _ = kwFunctor >> lpar >> binder >>= (fn v => colon >>
    modType () >>= (fn m1 => rpar >> rightarrow >>
    modExpr () >>= (fn m2 => return (MTS.ModFunctor (v, m1, m2)))))
  and modApp _ = modExpr () >>= (fn m1 => modExpr () >>= (fn m2 =>
    return (MTS.ModApp (m1, m2))))
  and modPath _ = path () >>= (fn p => return (MTS.ModPath p))
  and modType _ = modSig () ++ modFuncT ()
  and modSig _ = kwSig >> many (binder >>= (fn v =>
    colon >> specification () >>= (fn s => semicolon >>
    return ((v, v), s)))) >>= (fn vsl => return (MTS.ModTypeSig vsl))
  and modFuncT _ = kwFuncT >> lpar >> binder >>= (fn v => colon >>
    modType () >>= (fn m1 => rpar >> rightarrow >>
    modType () >>= (fn m2 => return (MTS.ModTypeFunctor (v, m1, m2)))))
end

