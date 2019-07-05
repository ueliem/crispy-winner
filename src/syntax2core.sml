structure RenameMonad = StateFunctor(type s = int)

structure Syntax2Core : 
sig
  val fresh : string -> Syntax.var RenameMonad.monad
  val rename_term : Syntax.term -> Syntax.term RenameMonad.monad
  val rename_decl : Syntax.declaration -> Syntax.declaration RenameMonad.monad
  val rename : Syntax.program -> Syntax.program RenameMonad.monad
end
=
struct
  open RenameMonad 

  fun fresh (v : string) : Syntax.var RenameMonad.monad =
    get >>= (fn s =>
    put (s + 1) >>= (fn _ =>
      return (Syntax.RenamedVar (s, v))
    ))

  fun rename_term (t : Syntax.term) : Syntax.term RenameMonad.monad = 
    case t of
      Syntax.Sort _ => return t
    | Syntax.Variable (x) => 
        (case x of
          Syntax.Anonymous => 
            return (Syntax.Variable (x))
        | Syntax.Var y => 
            return (Syntax.Variable (x))
        | Syntax.RenamedVar _ => 
            return (Syntax.Variable (x))
        )
    | Syntax.Literal _ => return t
    | Syntax.Abs (x, t1, t2) =>
        (case x of
          Syntax.Anonymous => 
            rename_term t1 >>= (fn t1' =>
            rename_term t2 >>= (fn t2' =>
                return (Syntax.Abs (x, t1', t2'))
            ))
        | Syntax.Var y => 
            fresh y >>= (fn u =>
            rename_term (Syntax.weak_replace y u t1) >>= (fn t1' =>
            rename_term (Syntax.weak_replace y u t2) >>= (fn t2' =>
                return (Syntax.Abs (u, t1', t2'))
            )))
        | Syntax.RenamedVar _ => raise Fail "should not happen ever")
    | Syntax.App (t1, t2) => 
        rename_term t1 >>= (fn t1' =>
        rename_term t2 >>= (fn t2' =>
          return (Syntax.App (t1', t2'))
        ))
    | Syntax.DepProd (x, t1, t2) =>
        (case x of
          Syntax.Anonymous => 
            rename_term t1 >>= (fn t1' =>
            rename_term t2 >>= (fn t2' =>
                return (Syntax.DepProd (x, t1', t2'))
            ))
        | Syntax.Var y => 
            fresh y >>= (fn u =>
            rename_term (Syntax.weak_replace y u t1) >>= (fn t1' =>
            rename_term (Syntax.weak_replace y u t2) >>= (fn t2' =>
                return (Syntax.DepProd (u, t1', t2'))
            )))
        | Syntax.RenamedVar _ => raise Fail "should not happen ever")
    | Syntax.Unknown => return t
    | Syntax.PrimApp (b, t1, t2) => 
        rename_term t1 >>= (fn t1' =>
        rename_term t2 >>= (fn t2' =>
          return (Syntax.PrimApp (b, t1', t2'))
        ))
    | Syntax.LetTerm (x, t1, t2, t3) =>
        (case x of
          Syntax.Anonymous => 
            rename_term t1 >>= (fn t1' =>
            rename_term t2 >>= (fn t2' =>
            rename_term t3 >>= (fn t3' =>
                return (Syntax.LetTerm (x, t1', t2', t3'))
            )))
        | Syntax.Var y => 
            fresh y >>= (fn u =>
            rename_term (Syntax.weak_replace y u t1) >>= (fn t1' =>
            rename_term (Syntax.weak_replace y u t2) >>= (fn t2' =>
            rename_term (Syntax.weak_replace y u t3) >>= (fn t3' =>
                return (Syntax.LetTerm (u, t1', t2', t3'))
            ))))
        | Syntax.RenamedVar _ => raise Fail "should not happen ever")
    | Syntax.DepSum (x, t1, t2) =>
        (case x of
          Syntax.Anonymous => 
            rename_term t1 >>= (fn t1' =>
            rename_term t2 >>= (fn t2' =>
                return (Syntax.DepSum (x, t1', t2'))
            ))
        | Syntax.Var y => 
            fresh y >>= (fn u =>
            rename_term (Syntax.weak_replace y u t1) >>= (fn t1' =>
            rename_term (Syntax.weak_replace y u t2) >>= (fn t2' =>
                return (Syntax.DepSum (u, t1', t2'))
            )))
        | Syntax.RenamedVar _ => raise Fail "should not happen ever")
    | Syntax.Pair (t1, t2) => 
        rename_term t1 >>= (fn t1' =>
        rename_term t2 >>= (fn t2' =>
          return (Syntax.Pair (t1', t2'))
        ))
    | Syntax.Fst t1 => 
        rename_term t1 >>= (fn t1' =>
          return (Syntax.Fst t1')
        )
    | Syntax.Snd t1 => 
        rename_term t1 >>= (fn t1' =>
          return (Syntax.Snd t1')
        )
    | Syntax.FuncType (t1, t2) => 
        rename_term t1 >>= (fn t1' =>
        rename_term t2 >>= (fn t2' =>
          return (Syntax.FuncType (t1', t2'))
        ))

  fun rename_decl (t : Syntax.declaration) : Syntax.declaration RenameMonad.monad = 
    case t of
      Syntax.Value (x, t1, t2) => 
        (case x of
          Syntax.Anonymous => raise Fail "makes no sense"
        | Syntax.Var y => 
            fresh y >>= (fn u =>
            rename_term (Syntax.weak_replace y u t1) >>= (fn t1' =>
            rename_term (Syntax.weak_replace y u t2) >>= (fn t2' =>
              return (Syntax.Value (u, t1', t2'))
            )))
        | Syntax.RenamedVar _ => raise Fail "makes no sense"
        )

  fun rename_decl_list (t : Syntax.declaration list) : Syntax.declaration list RenameMonad.monad = 
    case t of 
      [] => return ([])
    | (d::dl) =>
        (case d of
          Syntax.Value (x, t1, t2) => 
            (case x of
              Syntax.Anonymous => raise Fail "makes no sense"
            | Syntax.Var y => 
                fresh y >>= (fn u =>
                rename_term (Syntax.weak_replace y u t1) >>= (fn t1' =>
                rename_term (Syntax.weak_replace y u t2) >>= (fn t2' =>
                rename_decl_list (map (Syntax.weak_replace_decl y u) dl) >>= (fn dl' =>
                  return ((Syntax.Value (u, t1', t2'))::dl')
                ))))
            | Syntax.RenamedVar _ => raise Fail "makes no sense"
        ))

  fun rename (prog : Syntax.program) : Syntax.program RenameMonad.monad = 
    case prog of 
      Syntax.Prog dl =>
        rename_decl_list dl >>= (fn dl' =>
          return (Syntax.Prog dl')
        )

end

