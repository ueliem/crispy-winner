structure CoreFromSyntax = struct
  open MTSCompilerM
  open Syntax
  fun fromPath ([]) = throw (CompilerError "from path")
    | fromPath p =
      return (foldl (fn (v, m) => MTS.PPath (MTS.ModPath m, v))
        (MTS.PVar (hd p)) (tl p))
  and fromAnnotatedBinder (v, t) = fromTerm t >>= (fn t' => return (v, t'))
  and fromModtypeBinder (v, m) = fromModtype m >>= (fn m' => return (v, m'))
  and fromTerm (Path p) = fromPath p >>= (fn p' => return (MTS.Path p'))
    | fromTerm (Lit l) = return (MTS.Lit l)
    | fromTerm (Sort s) = return (MTS.Sort s)
    | fromTerm (App (t1, t2)) = fromTerm t1 >>= (fn t1' =>
      fromTerm t2 >>= (fn t2' => return (MTS.App (t1', t2'))))
  (* | fromTerm (Case of term * term * (path * var list * term) list *)
    | fromTerm (IfElse (t1, t2, t3)) =
      fromTerm t1 >>= (fn t1' => fromTerm t2 >>= (fn t2' =>
      fromTerm t3 >>= (fn t3' => return (MTS.IfElse (t1', t2', t3')))))
    | fromTerm (Let (v, t1, t2, t3)) =
      fromTerm t1 >>= (fn t1' => fromTerm t2 >>= (fn t2' =>
      fromTerm t3 >>= (fn t3' => return (MTS.Let (v, t1', t2', t3')))))
    | fromTerm (Lambda (args, t)) =
      let fun f (vt::args') = fromAnnotatedBinder vt >>= (fn (v, t1') =>
        f args' >>= (fn t2' => return (MTS.Lambda (v, t1', t2'))))
        | f ([]) = fromTerm t in f args end
    | fromTerm (DepProduct (args, t)) =
      let fun f (vt::args') = fromAnnotatedBinder vt >>= (fn (v, t1') =>
        f args' >>= (fn t2' => return (MTS.DepProduct (v, t1', t2'))))
        | f ([]) = fromTerm t in f args end
  and fromDef (DefTerm (v, t)) =
    fromTerm t >>= (fn t' => return (v, MTS.DefVal t'))
  (* | fromDef (DefTermTyped (v, t1, t2)) = *)
  | fromDef (DefMod (v, m)) =
    fromModexpr m >>= (fn m' => return (v, MTS.DefMod m'))
  (* | fromDef (DefModSig (v, m1, m2)) =
  | fromDef (DefModTransparent (v, m)) = *)
  (* | fromDef (DefInductive (v, t, vtl)) = *)
  and fromModtype (ModTypeSig sl) = raise Fail ""
  | fromModtype (ModTypeFunctor (args, m)) =
      let fun f (vm::args') = fromModtypeBinder vm >>= (fn (v, m1') =>
        f args' >>= (fn m2' => return (MTS.ModTypeFunctor (v, m1', m2'))))
        | f ([]) = fromModtype m in f args end
  (* and fromSpecification =
    SpecAbsMod of var * modtype
  | SpecManifestMod of var * modtype * modexpr
  | SpecAbsTerm of var * term
  | SpecManifestTerm of var * term * term
  | SpecInductive of var * term * (var * term) list *)
  and fromModexpr (ModStruct dl) = raise Fail ""
  | fromModexpr (ModFunctor (v, m1, m2)) =
     fromModtype m1 >>= (fn m1' => fromModexpr m2 >>= (fn m2' =>
     return (MTS.ModFunctor (v, m1', m2'))))
  | fromModexpr (ModApp (m1, m2)) =
     fromModexpr m1 >>= (fn m1' => fromModexpr m2 >>= (fn m2' =>
     return (MTS.ModApp (m1', m2'))))
  | fromModexpr (ModPath p) = fromPath p >>= (fn p' => return (MTS.ModPath p'))
  (* and fromToplvl =
    TopSpec of specification
  | TopDef of def
  type fromProgram = (var * toplvl) list
  *)
end
