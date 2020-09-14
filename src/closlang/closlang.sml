structure ClosLang :
sig
  val convProgram : ANFProgram.program -> ClosLangProgram.program ANF.ANFFVM.monad
  val convDecl : ANFProgram.declaration -> ClosLangProgram.declaration ANF.ANFFVM.monad
  val convTerm : ANFTerm.term -> ClosLangTerm.term ANF.ANFFVM.monad
end
=
struct
  open ANF.ANFFVM

  fun convTerm (ANFTerm.Return (m)) =
      return (ClosLangTerm.Return (m))
  | convTerm (ANFTerm.Let (x, m1, m2)) =
      convTerm m2 >>= (fn m2' =>
      (case m1 of 
        ANFTerm.Value v =>
          (case v of
            (ANFTerm.IntLit i) =>
              return (ClosLangTerm.Let (x, ClosLangTerm.Value
                (ClosLangTerm.IntLit i), m2'))
          | (ANFTerm.BoolLit b) =>
              return (ClosLangTerm.Let (x, ClosLangTerm.Value
                (ClosLangTerm.BoolLit b), m2'))
          | (ANFTerm.UnitLit) =>
              return (ClosLangTerm.Let (x, ClosLangTerm.Value
                (ClosLangTerm.UnitLit), m2'))
          | (ANFTerm.Lambda (rs, args, m)) =>
              convTerm m >>= (fn m' =>
                let
                  val fv = Set.toList (ANFTerm.freevarsTerm args m)
                in
                  if List.length fv > 0 then
                    fresh >>= (fn v' =>
                    let
                      fun f i ([]) n = n
                      | f i (v::vl) n =
                          ClosLangTerm.Let (v, ClosLangTerm.Select (i, v'), f (i + 1) vl n)
                    in
                        return (ClosLangTerm.Let (v', ClosLangTerm.Value
                          (ClosLangTerm.Tuple fv),
                            (ClosLangTerm.Let (x, ClosLangTerm.Value
                              (ClosLangTerm.Closure (f 0 fv m',
                                (List.length args) + 1, [v'])), m2'))))
                    end
                    )
                  else
                    return (ClosLangTerm.Let (x, ClosLangTerm.Value
                      (ClosLangTerm.Closure (m', List.length args, [])), m2'))
                end
              )
          | (ANFTerm.Tuple m) =>
              return (ClosLangTerm.Let (x, ClosLangTerm.Value
                (ClosLangTerm.Tuple m), m2'))
          )
      | ANFTerm.Var v =>
          return (ClosLangTerm.Let (x, ClosLangTerm.Var v, m2'))
      | ANFTerm.Select (i, m) =>
          return (ClosLangTerm.Let (x, ClosLangTerm.Select (i, m), m2'))
      | ANFTerm.Box (m, r) =>
          return (ClosLangTerm.Let (x, ClosLangTerm.Box (m, r), m2'))
      | ANFTerm.Unbox m =>
          return (ClosLangTerm.Let (x, ClosLangTerm.Unbox m, m2'))
      | ANFTerm.RegionElim (rs, m) =>
          return (ClosLangTerm.Let (x, ClosLangTerm.RegionElim (rs, m), m2'))
      | ANFTerm.App (m1, m2) =>
          return (ClosLangTerm.Let (x, ClosLangTerm.App (m1, m2), m2'))
      | ANFTerm.PrimApp (opr, m) =>
          return (ClosLangTerm.Let (x, ClosLangTerm.PrimApp (opr, m), m2'))
      ))
  | convTerm (ANFTerm.LetRegion (r, m)) =
      convTerm m >>= (fn m' =>
        return (ClosLangTerm.LetRegion (r, m'))
      )
  | convTerm (ANFTerm.IfElse (m1, m2, m3)) =
      convTerm m2 >>= (fn m2' =>
      convTerm m3 >>= (fn m3' =>
        return (ClosLangTerm.IfElse (m1, m2', m3'))
      ))

  and convDecl (ANFProgram.DeclType (v, t)) = raise Fail ""
  | convDecl (ANFProgram.DeclVal (v, t, m)) =
      convTerm m >>= (fn m' =>
        return (ClosLangProgram.DeclVal (v, t, m'))
      )
  | convDecl (ANFProgram.DeclFun (v, argv, argt, rt, m)) = raise Fail ""

  fun convProgram (ANFProgram.Prog (dl)) =
    let
      fun f ([]) = return ([])
      | f (d::ds) =
          convDecl d >>= (fn d' =>
          (f ds) >>= (fn ds' =>
            return (d'::ds')
          ))
    in
      f dl >>= (fn dl' =>
        return (ClosLangProgram.Prog dl')
      )
    end

end

