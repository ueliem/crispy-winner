structure CoreFromSyntax = struct
  open MTSCompilerM
  open Syntax
  structure Util = MTSCompilerMUtil
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
      Util.foldM (fn y => (fn x => fromTerm x >>= (fn x' =>
        return (MTS.App (y, x'))))) t1' t2)
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
  | fromDef (DefTermTyped (v, t1, t2)) = raise Fail "Not implemented"
  | fromDef (DefMod (v, m)) =
    fromModexpr m >>= (fn m' => return (v, MTS.DefMod m'))
  | fromDef (DefModSig (v, m1, m2)) =
    fromModexpr m1 >>= (fn m1' => fromModtype m2 >>= (fn m2' =>
      return (v, MTS.DefModSig (m1', m2'))))
  | fromDef (DefModTransparent (v, m)) =
    fromModexpr m >>= (fn m' => return (v, MTS.DefModTransparent m'))
  (* | fromDef (DefInductive (v, t, vtl)) = *)
  and fromModtype (ModTypeSig sl) = raise Fail ""
  | fromModtype (ModTypeFunctor (args, m)) =
      let fun f (vm::args') = fromModtypeBinder vm >>= (fn (v, m1') =>
        f args' >>= (fn m2' => return (MTS.ModTypeFunctor (v, m1', m2'))))
        | f ([]) = fromModtype m in f args end
  and fromSpecification (SpecAbsMod (v, m)) =
    fromModtype m >>= (fn m' => return (v, MTS.SpecAbsMod m'))
  | fromSpecification (SpecManifestMod (v, m1, m2)) =
    fromModexpr m2 >>= (fn m2' => fromModtype m1 >>= (fn m1' =>
      return (v, MTS.SpecManifestMod (m1', m2'))))
  | fromSpecification (SpecAbsTerm (v, t)) =
    fromTerm t >>= (fn t' => return (v, MTS.SpecAbsTerm t'))
  | fromSpecification (SpecManifestTerm (v, t1, t2)) =
    fromTerm t1 >>= (fn t1' => fromTerm t2 >>= (fn t2' =>
      return (v, MTS.SpecManifestTerm (t1', t2'))))
  (* | fromSpecification (SpecInductive (v, t, vtl)) = *)
  and fromModexpr (ModStruct dl) = raise Fail ""
  | fromModexpr (ModFunctor (v, m1, m2)) =
     fromModtype m1 >>= (fn m1' => fromModexpr m2 >>= (fn m2' =>
       return (MTS.ModFunctor (v, m1', m2'))))
  | fromModexpr (ModApp (m1, m2)) =
     fromModexpr m1 >>= (fn m1' => fromModexpr m2 >>= (fn m2' =>
       return (MTS.ModApp (m1', m2'))))
  | fromModexpr (ModPath p) = fromPath p >>= (fn p' => return (MTS.ModPath p'))
end
