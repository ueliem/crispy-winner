structure ANF :
sig
  structure ANFFVM : 
  sig
    include MONAD
    val fresh : ANFTerm.var monad
  end
  val normalizeprogram : Program.program -> ANFProgram.program ANFFVM.monad
  val normalizedecl : Program.declaration -> ANFProgram.declaration ANFFVM.monad
  val normalize : Term.term -> ANFTerm.term ANFFVM.monad
  val normalizeterm : Term.term -> (ANFTerm.term -> ANFTerm.term ANFFVM.monad) -> ANFTerm.term ANFFVM.monad
  val normalizename : Term.term -> (ANFTerm.var -> ANFTerm.term ANFFVM.monad) -> ANFTerm.term ANFFVM.monad
  val normalizenames : Term.term list -> (ANFTerm.var list -> ANFTerm.term ANFFVM.monad) -> ANFTerm.term ANFFVM.monad
  val normalizevalue : Term.value -> (ANFTerm.var -> ANFTerm.term ANFFVM.monad) -> ANFTerm.term ANFFVM.monad
end
=
struct
  structure ANFFVM = FreshVarMonad (type v = ANFTerm.var; fun f i = ANFTerm.GenVar i)
  open ANFFVM
  
  fun normalizeprogram (Program.Prog (dl)) =
    let
      fun f ([]) = return ([])
      | f (d::ds) =
          normalizedecl d >>= (fn d' =>
          (f ds) >>= (fn ds' =>
            return (d'::ds')
          ))
    in
      f dl >>= (fn dl' =>
        return (ANFProgram.Prog dl')
      )
    end

  and normalizedecl (Program.DeclType (v, t)) =
      return (ANFProgram.DeclType (ANFTerm.NamedVar (v), t))
  | normalizedecl (Program.DeclVal (v, t, m)) =
      normalize m >>= (fn m' =>
        return (ANFProgram.DeclVal (ANFTerm.NamedVar (v), t, m'))
      )
  | normalizedecl (Program.DeclFun (v, argv, argt, rt, m)) = raise Fail ""

  and normalize m = normalizeterm m (fn x => return x)

  and normalizeterm (Term.Value v) k =
      normalizevalue v (fn v' =>
      fresh >>= (fn v'' => 
      (k (ANFTerm.AtomTerm (ANFTerm.Var v''))) >>= (fn e =>
        return (ANFTerm.Let (v'', ANFTerm.Atom (ANFTerm.Var v'), e))
      )))
  | normalizeterm (Term.Var v) k =
      k (ANFTerm.AtomTerm (ANFTerm.Var (ANFTerm.NamedVar v)))
  | normalizeterm (Term.Select (i, m)) k =
      normalizename m (fn v =>
      fresh >>= (fn v' =>
      (k (ANFTerm.AtomTerm (ANFTerm.Var v'))) >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.Select (i, ANFTerm.Var v), e))
      )))
  | normalizeterm (Term.Box (m, r)) k =
      normalizename m (fn v =>
      fresh >>= (fn v' =>
      (k (ANFTerm.AtomTerm (ANFTerm.Var v'))) >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.Box (ANFTerm.Var v, r), e))
      )))
  | normalizeterm (Term.Unbox m) k =
      normalizename m (fn v =>
      fresh >>= (fn v' =>
      (k (ANFTerm.AtomTerm (ANFTerm.Var v'))) >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.Unbox (ANFTerm.Var v), e))
      )))
  | normalizeterm (Term.Let (x, m1, m2, argt)) k =
      normalizename m1 (fn v =>
      fresh >>= (fn v' => 
      normalizeterm m2 k >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.Atom (ANFTerm.Var v), e))
      )))
  | normalizeterm (Term.LetRegion (r, m)) k =
      normalizeterm m k >>= (fn m' =>
        return (ANFTerm.LetRegion (r, m'))
      )
  | normalizeterm (Term.IfElse (m1, m2, m3)) k =
      normalizename m1 (fn v =>
      normalizeterm m2 k >>= (fn e1 =>
      normalizeterm m3 k >>= (fn e2 =>
        return (ANFTerm.IfElse (ANFTerm.Var v, e1, e2))
      )))
  | normalizeterm (Term.RegionElim (rs, m)) k =
      normalizename m (fn (v : ANFTerm.var) =>
      fresh >>= (fn (v' : ANFTerm.var) =>
      (k (ANFTerm.AtomTerm (ANFTerm.Var v'))) >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.RegionElim (rs, ANFTerm.Var v), e))
      )))
  | normalizeterm (Term.App (m1, m2)) k =
      normalizename m1 (fn v =>
      normalizenames m2 (fn argv =>
      fresh >>= (fn v' => 
      (k (ANFTerm.AtomTerm (ANFTerm.Var v'))) >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.App (ANFTerm.Var v,
          map (fn v' => ANFTerm.Var v') argv), e))
      ))))
  | normalizeterm (Term.PrimApp (opr, m)) k =
      normalizenames m (fn argv =>
      fresh >>= (fn v' => 
      (k (ANFTerm.AtomTerm (ANFTerm.Var v'))) >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.PrimApp (opr,
          map (fn v' => ANFTerm.Var v') argv), e))
      )))

  and normalizename (Term.Value v) k = normalizevalue v k
  | normalizename (Term.Var v) k = k (ANFTerm.NamedVar v)
  | normalizename (Term.Select (i, m)) k =
      normalizename m (fn v =>
      fresh >>= (fn v' => 
      (k v') >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.Select (i, ANFTerm.Var v), e))
      )))
  | normalizename (Term.Box (m, r)) k =
      normalizename m (fn v =>
      fresh >>= (fn v' => 
      (k v') >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.Box (ANFTerm.Var v, r), e))
      )))
  | normalizename (Term.Unbox m) k =
      normalizename m (fn v =>
      fresh >>= (fn v' => 
      (k v') >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.Unbox (ANFTerm.Var v), e))
      )))
  | normalizename (Term.Let (x, m1, m2, argt)) k =
      normalizename m1 (fn v =>
      fresh >>= (fn v' => 
      normalizename m2 k >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.Atom (ANFTerm.Var v), e))
      )))
  | normalizename (Term.LetRegion (r, m)) k =
      normalizename m k >>= (fn m' =>
        return (ANFTerm.LetRegion (r, m'))
      )
  | normalizename (Term.IfElse (m1, m2, m3)) k =
      normalizename m1 (fn v =>
      normalizename m2 k >>= (fn e1 =>
      normalizename m3 k >>= (fn e2 =>
        return (ANFTerm.IfElse (ANFTerm.Var v, e1, e2))
      )))
  | normalizename (Term.RegionElim (rs, m)) k =
      normalizename m (fn v =>
      fresh >>= (fn v' => 
      (k v') >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.RegionElim (rs, ANFTerm.Var v), e))
      )))
  | normalizename (Term.App (m1, m2)) k =
      normalizename m1 (fn v =>
      normalizenames m2 (fn argv =>
      fresh >>= (fn v' => 
      (k v') >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.App (ANFTerm.Var v,
          map (fn v' => ANFTerm.Var v') argv), e))
      ))))
  | normalizename (Term.PrimApp (opr, m)) k =
      normalizenames m (fn argv =>
      fresh >>= (fn v' => 
      (k v') >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.PrimApp (opr,
          map (fn v' => ANFTerm.Var v') argv), e))
      )))

  and normalizenames (tl) k = normnames [] tl k

  and normnames vl ([]) k = k (List.rev vl)
  | normnames vl (m::ml) k =
    normalizename m (fn v =>
      normnames (v::vl) ml k
    )

  and normalizevalue (Term.IntLit i) k =
      fresh >>= (fn v' => 
      (k v') >>= (fn e =>
        return (ANFTerm.Let (v',
          ANFTerm.Atom (ANFTerm.Value (ANFTerm.IntLit i)), e))
      ))
  | normalizevalue (Term.BoolLit b) k =
      fresh >>= (fn v' => 
      (k v') >>= (fn e =>
        return (ANFTerm.Let (v',
          ANFTerm.Atom (ANFTerm.Value (ANFTerm.BoolLit b)), e))
      ))
  | normalizevalue (Term.UnitLit) k =
      fresh >>= (fn v' => 
      (k v') >>= (fn e =>
        return (ANFTerm.Let (v',
          ANFTerm.Atom (ANFTerm.Value (ANFTerm.UnitLit)), e))
      ))
  | normalizevalue (Term.Lambda (rs, args, rt, phi, m)) k =
      fresh >>= (fn v' => 
      normalize m >>= (fn m' =>
      (k v') >>= (fn e =>
        return (ANFTerm.Let (v', ANFTerm.Atom (ANFTerm.Value (
          ANFTerm.Lambda (rs, map (fn x => ANFTerm.NamedVar x)
            (#1 (ListPair.unzip args)), m'))), e))
      )))
  | normalizevalue (Term.Tuple m) k = 
      normalizenames m (fn argv =>
      fresh >>= (fn v' => 
      (k v') >>= (fn e =>
        return (ANFTerm.Let (v',
          ANFTerm.Atom (ANFTerm.Value (
            ANFTerm.Tuple (map (fn v' => ANFTerm.Var v') argv))), e))
      )))

end

