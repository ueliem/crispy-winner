structure SyntaxParser : sig
  include PARSER
  structure M : MONAD
  structure TSP : PARSER
  val binder : MTS.var monad
  val ptsLiteral : MTS.term monad
  val ptsSort : MTS.term monad
  val annotatedBinder : unit -> (MTS.var * MTS.term) monad
  val path : unit -> MTS.path monad
  val def : unit -> (MTS.var * MTS.def) list monad
  val specification : unit -> MTS.specification monad
  val ptsTerm : unit -> MTS.term monad
  val ptsPath : unit -> MTS.term monad
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
  structure M = MTSCompilerM
  structure TSP = MTSTokenParser
  open TSP
  open MTSTokenParserUtil
  val binder = (ident >>= (fn v => return (MTS.NamedVar v)))
    ++ (underscore >> return (MTS.AnonVar))
  val ptsLiteral = (kwInt >> return (MTS.Lit (MTS.IntTyLit)))
    ++ (kwBool >> return (MTS.Lit (MTS.BoolTyLit)))
    ++ (intLit >>= (fn i => return (MTS.Lit (MTS.IntLit i))))
    ++ (boolLit >>= (fn b => return (MTS.Lit (MTS.BoolLit b))))
  val ptsSort = (kwSet >> return (MTS.Sort (MTS.TypeVal)))
    ++ (kwType >> return (MTS.Sort (MTS.KindVal)))
    ++ (kwComp >> return (MTS.Sort (MTS.TypeComp)))
    ++ (kwTrans >> return (MTS.Sort (MTS.KindComp)))
  fun annotatedBinder () = lpar >> binder >>= (fn v => colon >>
    ptsTerm () >>= (fn t => rpar >> return (v, t)))
  and path () = (binder >>= (fn v => return (MTS.PVar v)))
    ++ (modExpr () >>= (fn m => period >> binder >>= (fn v =>
      return (MTS.PPath (m, v)))))
  and def _ = (kwVal >> binder >>= (fn v => defined >>
    ptsTerm () >>= (fn t => return [(v, MTS.DefVal t)])))
    ++ (kwModule >> binder >>= (fn v => defined >>
      (kwTransparent >> modExpr () >>= (fn m =>
        return [(v, MTS.DefModTransparent m)]))
      ++ (modExpr () >>= (fn m1 => colon >> modType () >>= (fn m2 =>
        return [(v, MTS.DefModSig (m1, m2))])))
      ++ (modExpr () >>= (fn m => return [(v, MTS.DefMod m)]))))
    ++ (kwInductive >> binder >>= (fn v => colon >>
      ptsTerm () >>= (fn t => defined >>
      many (pipe >> binder >>= (fn v' =>
      colon >> ptsTerm () >>= (fn t' => return (v', t')))) >>= (fn dcl =>
      let val (vs, ts) = ListPair.unzip dcl in
        return ((v, MTS.DefVal (MTS.Inductive ((v, t), ts)))
          ::(List.tabulate (List.length dcl,
            (fn i => (List.nth (vs, i), MTS.DefVal
              (MTS.Constr (i, MTS.Path (MTS.PVar v))))))))end))))
  and specification _ =
    (ptsTerm () >>= (fn t => return (MTS.SpecAbsTerm t)))
    ++ (ptsTerm () >>= (fn t1 => defined >> ptsTerm () >>= (fn t2 =>
      return (MTS.SpecManifestTerm (t1, t2)))))
    ++ (modType () >>= (fn m => return (MTS.SpecAbsMod m)))
    ++ (modType () >>= (fn m1 => defined >> modExpr () >>= (fn m2 =>
      return (MTS.SpecManifestMod (m1, m2)))))
  and ptsTerm () = ptsPath () ++ ptsLiteral ++ ptsSort
    ++ ptsApp () ++ ptsCase () ++ ptsIfElse ()
    ++ ptsLet () ++ ptsLambda () ++ ptsDepProduct ()
  and ptsPath () = path () >>= (fn p => return (MTS.Path p))
  and ptsApp () = ptsTerm () >>= (fn t1 => ptsTerm () >>= (fn t2 =>
    return (MTS.App (t1, t2))))
  and ptsCase () = let fun ptsAlt _ =
    binder >>= (fn c => many binder >>= (fn vs =>
    rightarrow >> ptsTerm () >>= (fn t' => return (c, vs, t'))))
    in kwCase >> ptsTerm () >>= (fn t => kwOf >>
      ptsAlt () >>= (fn x => many1 (pipe >> ptsAlt ()) >>= (fn xs =>
      (* return (MTS.Case (t, x::xs)) *) raise Fail ""))) end
  and ptsIfElse () = kwIf >> ptsTerm () >>= (fn t1 =>
    kwThen >> ptsTerm () >>= (fn t2 =>
    kwElse >> ptsTerm () >>= (fn t3 =>
    return (MTS.IfElse (t1, t2, t3)))))
  and ptsLet () = kwLet >> annotatedBinder () >>= (fn (v, t1) =>
    defined >> ptsTerm () >>= (fn t2 =>
    kwIn >> ptsTerm () >>= (fn t3 =>
    kwEnd >> return (MTS.Let (v, t1, t2, t3)))))
  and ptsLambda () = kwFun >> annotatedBinder () >>= (fn (v, t1) =>
    rightarrow >> ptsTerm () >>= (fn t2 =>
    return (MTS.Lambda (v, t1, t2))))
  and ptsDepProduct () = kwForAll >> annotatedBinder () >>= (fn (v, t1) =>
    rightarrow >> ptsTerm () >>= (fn t2 =>
    return (MTS.DepProduct (v, t1, t2))))
  and modExpr _ =
    modStruct () ++ modFunctor () ++ modApp () ++ modPath ()
  and modStruct _ = kwStruct >> many (def ()) >>= (fn vdl =>
    kwEnd >> return (MTS.ModStruct (List.concat vdl)))
  and modFunctor _ = kwFunctor >> lpar >> binder >>= (fn v => colon >>
    modType () >>= (fn m1 => rpar >> rightarrow >>
    modExpr () >>= (fn m2 => return (MTS.ModFunctor (v, m1, m2)))))
  and modApp _ = modExpr () >>= (fn m1 => modExpr () >>= (fn m2 =>
    return (MTS.ModApp (m1, m2))))
  and modPath _ = path () >>= (fn p => return (MTS.ModPath p))
  and modType _ = modSig () ++ modFuncT ()
  and modSig _ = kwSig >> many (binder >>= (fn v =>
    colon >> specification () >>= (fn s => semicolon >>
    return (v, s)))) >>= (fn vsl => kwEnd >> return (MTS.ModTypeSig vsl))
  and modFuncT _ = kwFuncT >> lpar >> binder >>= (fn v => colon >>
    modType () >>= (fn m1 => rpar >> rightarrow >>
    modType () >>= (fn m2 => return (MTS.ModTypeFunctor (v, m1, m2)))))
end

