structure TypeCheckMonad : sig
  datatype 'a typecheckresult =
    Ok of 'a
  | Error
  include MONAD where type 'a monad = 'a typecheckresult
  val fail : unit -> 'a monad
end
=
struct
  datatype 'a typecheckresult =
    Ok of 'a
  | Error
  type 'a monad = 'a typecheckresult
  fun return x = Ok (x)
  fun op >>= (m, f) = 
    case m of
      Ok x => f x
    | Error => Error
  val fail = (fn _ => Error)
end

structure TypeCheck : sig
  type typeenv = (Term.var * Ty.ty) list
  type regionenv = RegionSet.regionset

  val checkValue : typeenv -> regionenv -> Term.value -> (Ty.ty * RegionSet.effect) TypeCheckMonad.monad
  val checkTerm : typeenv -> regionenv -> Term.term -> (Ty.ty * RegionSet.effect) TypeCheckMonad.monad
  val checkProgram : Program.program -> ((Ty.ty * RegionSet.effect) list) TypeCheckMonad.monad
end
=
struct
  type typeenv = (Term.var * Ty.ty) list
  type regionenv = RegionSet.regionset
  open TypeCheckMonad
  open Ty
  open Term
  open Program

  fun checkProgram (Prog dl) =
    let
      fun checkDecl tenv renv ([]) = return []
      | checkDecl tenv renv (d::dl) =
          (case d of
            Program.DeclType (v, t) => raise Fail "declty"
          | Program.DeclVal (v, t, m) =>
              checkTerm tenv renv m >>= (fn (t', phi') =>
                let
                  val _ = PolyML.print (Ty.tostring t)
                  val _ = PolyML.print (Ty.tostring t')
                in
                  if eqty (t, t') then
                    checkDecl ((v, t)::tenv) renv (dl) >>= (fn tp' =>
                      return ((t', phi')::tp')
                    )
                  else raise Fail "declval1"
                end
              )
          | Program.DeclFun (v, vl, tl, t, m) => raise Fail "declfun")
    in
      checkDecl [] Set.emptyset dl
    end

  and checkTerm tenv renv (Value v) = checkValue tenv renv v
  | checkTerm tenv renv (Var v) = 
      (case List.find (fn x => #1 x = v) tenv of
        SOME (_, t) => return (t, Set.emptyset)
      | NONE => raise Fail "VarNotInEnv"
      )
  | checkTerm tenv renv (Select (i, m)) =
      checkTerm tenv renv m >>= (fn (t, phi) =>
        (case t of
          BoxedTy (TupleTy t1, r) => return (List.nth (t1, i), Set.insert r phi)
        | _ => raise Fail "sel1")
      )
  | checkTerm tenv renv (Box m) = raise Fail "box1"
  | checkTerm tenv renv (Unbox m) =
      checkTerm tenv renv m >>= (fn (t, phi) =>
        return (t, phi)
      )
  | checkTerm tenv renv (Let (x, m1, m2, argt)) = 
      checkTerm tenv renv m1 >>= (fn (t1, phi1) =>
      checkTerm tenv renv m2 >>= (fn (t2, phi2) =>
        if eqty (t1, argt) then return (t2, Set.union phi1 phi2)
        else raise Fail "let1"
      ))
  | checkTerm tenv renv (LetRegion (r, m)) = 
      checkTerm tenv (Set.insert r renv) m >>= (fn (t, phi) =>
        return (t, Set.remove r phi)
      )
  | checkTerm tenv renv (RegionElim (rs, m)) = 
      checkTerm tenv renv m >>= (fn (t, phi) =>
        (case t of
          BoxedTy (FuncTy (rsf, tl, rt, phi1), r) => 
            let
              val substs = (ListPair.zipEq (Set.toList rsf, Set.toList rs))
            in
              if Set.member r renv then
                return (BoxedTy (FuncTy (Set.emptyset, 
                  map (fn ft => foldl (fn (sbt, argt) => substRegVarTy sbt argt) ft substs) tl,
                  foldl (fn (sbt, argt) => Ty.substRegVarTy sbt argt) rt substs,
                  foldl (fn (sbt, s) => RegionSet.substRegVarRegSet sbt s) phi1 substs),
                  r), Set.singleton r)
              else raise Fail "elim2"
            end
        | _ => raise Fail "elim1"
      ))
  | checkTerm tyenv regenv (IfElse (m1, m2, m3)) = 
      checkTerm tyenv regenv m1 >>= (fn (t1, phi1) =>
      checkTerm tyenv regenv m2 >>= (fn (t2, phi2) =>
      checkTerm tyenv regenv m3 >>= (fn (t3, phi3) =>
        (case t1 of
          BoolTy =>
            if eqty (t2, t3) then return (t2, Set.union (Set.union phi1 phi2) phi3)
            else raise Fail "ifelse2"
        | _ => raise Fail "ifelse1")
      )))
  | checkTerm tyenv regenv (App (m1, m2)) = 
      checkTerm tyenv regenv m1 >>= (fn (t1, phi1) =>
      checkTermList tyenv regenv m2 >>= (fn (t2, phi2) =>
        (case t1 of
          BoxedTy (FuncTy (rsf, tl, rt, phi3), r) => 
            if Set.isempty rsf andalso 
              List.all (fn x => x = true) (map eqty (ListPair.zipEq (tl, t2)))
            then return (rt, Set.insert r (Set.union phi1 (Set.union phi2 phi3)))
            else raise Fail "app2"
        | _ => raise Fail "app1")
      ))
  | checkTerm tyenv regenv (PrimApp (opr, m)) = 
      checkTermList tyenv regenv m >>= (fn (t, phi) =>
        if List.length t = 2 then
          (case (List.nth (t, 0), List.nth (t, 1)) of
            (IntTy, IntTy) => 
              (case opr of
                "+" => return (IntTy, phi)
              | "-" => return (IntTy, phi)
              | "*" => return (IntTy, phi)
              | "<" => return (BoolTy, phi)
              | "=" => return (BoolTy, phi)
              | _ => raise Fail "undefined operator"
              ))
        else raise Fail "do not have anything other than binops yet"
      )
  and checkTermList tyenv regenv m =
      let
        fun f ([]) = return ([], Set.emptyset)
        | f (x::xs) = 
            checkTerm tyenv regenv x >>= (fn (t, phi) =>
            f xs >>= (fn (tl, phi1) =>
              return (t::tl, Set.union phi phi1)
            ))
      in
        f m
      end

  and checkValue tenv renv (IntLit _) = return (IntTy, Set.emptyset)
  | checkValue tenv renv (BoolLit _) = return (BoolTy, Set.emptyset)
  | checkValue tenv renv (UnitLit) = return (UnitTy, Set.emptyset)
  | checkValue tenv renv (Lambda (rs, args, rt, phi, m)) =
      if Set.isempty rs then
        checkTerm (args @ tenv) renv m >>= (fn (rt', phi') =>
          if eqty (rt, rt') andalso Set.eq phi phi' then
            return (FuncTy (rs, #2 (ListPair.unzip args), rt, phi), Set.emptyset)
          else
            raise Fail ""
        )
      else
          raise Fail ""
  | checkValue tenv renv (Tuple m) =
      let
        fun f ([]) = return ([], Set.emptyset)
        | f (x::xs) = 
            (checkTerm tenv renv x >>= (fn (t, phi) =>
            f xs >>= (fn (tl, phi1) =>
              return (t::tl, Set.union phi phi1)
            )))
      in
        f m >>= (fn (tl, phi) =>
          return (TupleTy tl, phi)
        )
      end

end

