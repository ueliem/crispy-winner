structure ANF : sig
  structure FreshVarMonad : MONAD

  datatype var = 
    V of string
  | GenV of int

  type regionvar = string
  type pointername = int
  type effect = regionvar Set.set
  type operator = string

  datatype boxty = 
    BoxIntTy of regionvar
  | BoxBoolTy of regionvar
  | BoxUnitTy of regionvar
  | BoxTupleTy of ty * ty * regionvar
  | BoxFuncTy of ty * ty * effect * regionvar
  | BoxRegFuncTy of regionvar * ty * effect * regionvar

  and ty =
    IntTy
  | BoolTy
  | UnitTy
  | TupleTy of ty * ty
  | BoxedTy of boxty

  datatype abs = 
    Lambda of var * term * ty * regionvar
  | RegionLambda of regionvar * abs * regionvar
  
  and value =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  | Tuple of term * term
  | BarePointer of regionvar * pointername

  and boxvalue = 
    BoxIntLit of int * regionvar
  | BoxBoolLit of bool * regionvar
  | BoxUnitLit of regionvar
  | BoxAbs of abs
  | BoxTuple of term * term * regionvar
  | BoxBarePointer of regionvar * pointername * regionvar

  and atom = 
    Var of var
  | Value of value
  | BoxedValue of boxvalue

  and comp =
    Atom of atom
  | App of atom * atom
  | PrimApp of operator * atom * atom
  | First of atom
  | Second of atom
  | Unbox of atom
  | RegionElim of atom * regionvar
  | IfElse of atom * term * term

  and term = 
    Comp of comp
  | Let of var * comp * term
  | LetRegion of regionvar * term

  val substRegVarBoxTy : (regionvar * regionvar) -> boxty -> boxty
  val substRegVarTy : (regionvar * regionvar) -> ty -> ty
  val substRegVar : (regionvar * regionvar) -> term -> term
  val substRegVarComp : (regionvar * regionvar) -> comp -> comp
  val substRegVarAtom : (regionvar * regionvar) -> atom -> atom
  val substRegVarValue : (regionvar * regionvar) -> value -> value
  val substRegVarBoxValue : (regionvar * regionvar) -> boxvalue -> boxvalue
  val substRegVarAbs : (regionvar * regionvar) -> abs -> abs

  val freshvar : unit -> var FreshVarMonad.monad
  val transformTerm : Lang.term -> term FreshVarMonad.monad
  val transformComp : Lang.term -> comp FreshVarMonad.monad
  val transformAtom : Lang.term -> atom FreshVarMonad.monad
  (* val transformValue : Lang.value -> atom FreshVarMonad.monad
  val transformBoxValue : Lang.boxvalue -> atom FreshVarMonad.monad *)

  val isValue : term -> bool
end
=
struct
  datatype var = 
    V of string
  | GenV of int

  type regionvar = string
  type pointername = int
  type effect = regionvar Set.set
  type operator = string

  datatype boxty = 
    BoxIntTy of regionvar
  | BoxBoolTy of regionvar
  | BoxUnitTy of regionvar
  | BoxTupleTy of ty * ty * regionvar
  | BoxFuncTy of ty * ty * effect * regionvar
  | BoxRegFuncTy of regionvar * ty * effect * regionvar

  and ty =
    IntTy
  | BoolTy
  | UnitTy
  | TupleTy of ty * ty
  | BoxedTy of boxty

  datatype abs = 
    Lambda of var * term * ty * regionvar
  | RegionLambda of regionvar * abs * regionvar
  
  and value =
    IntLit of int
  | BoolLit of bool
  | UnitLit
  | Tuple of term * term
  | BarePointer of regionvar * pointername

  and boxvalue = 
    BoxIntLit of int * regionvar
  | BoxBoolLit of bool * regionvar
  | BoxUnitLit of regionvar
  | BoxAbs of abs
  | BoxTuple of term * term * regionvar
  | BoxBarePointer of regionvar * pointername * regionvar

  and atom = 
    Var of var
  | Value of value
  | BoxedValue of boxvalue

  and comp =
    Atom of atom
  | App of atom * atom
  | PrimApp of operator * atom * atom
  | First of atom
  | Second of atom
  | Unbox of atom
  | RegionElim of atom * regionvar
  | IfElse of atom * term * term

  and term = 
    Comp of comp
  | Let of var * comp * term
  | LetRegion of regionvar * term

  structure M = StateFunctor (type s = int)
  structure FreshVarMonad = ContinuationT (type r = term; structure M = M)
  open FreshVarMonad

  fun liftedCallCC f =
    M.State (fn s =>
      callCC (fn c =>
        M.runState (f (fn a => M.State (fn s' => c (a, s')))) s
    ))

  fun substRegVarBoxTy (dst, newr) (BoxIntTy rho) = 
      BoxIntTy (if dst = rho then newr else rho)
  | substRegVarBoxTy (dst, newr) (BoxBoolTy rho) = 
      BoxBoolTy (if dst = rho then newr else rho)
  | substRegVarBoxTy (dst, newr) (BoxUnitTy rho) = 
      BoxUnitTy (if dst = rho then newr else rho)
  | substRegVarBoxTy (dst, newr) (BoxTupleTy (t1, t2 , rho)) = 
      BoxTupleTy (substRegVarTy (dst, newr) t1, 
        substRegVarTy (dst, newr) t2,
        if dst = rho then newr else rho)
  | substRegVarBoxTy (dst, newr) (BoxFuncTy (t1, t2, phi, rho)) =
      BoxFuncTy (substRegVarTy (dst, newr) t1, 
        substRegVarTy (dst, newr) t2,
        map (fn r => if dst = r then newr else r) phi,
        if dst = rho then newr else rho)
  | substRegVarBoxTy (dst, newr) (BoxRegFuncTy (rv, t, phi, rho)) =
      BoxRegFuncTy (rv, substRegVarTy (dst, newr) t,
        map (fn r => if dst = r then newr else r) phi,
        if dst = rho then newr else rho)

  and substRegVarTy (dst, newr) (IntTy) = IntTy
  | substRegVarTy (dst, newr) (BoolTy) = BoolTy
  | substRegVarTy (dst, newr) (UnitTy) = UnitTy
  | substRegVarTy (dst, newr) (TupleTy (t1, t2)) = 
      TupleTy (substRegVarTy (dst, newr) t1, substRegVarTy (dst, newr) t2)
  | substRegVarTy (dst, newr) (BoxedTy t) = 
      BoxedTy (substRegVarBoxTy (dst, newr) t)

  fun substRegVarAtom (dst, newr) (Var v) = Var v
  | substRegVarAtom (dst, newr) (Value v) = Value (substRegVarValue (dst, newr) v)
  | substRegVarAtom (dst, newr) (BoxedValue v) = 
      BoxedValue (substRegVarBoxValue (dst, newr) v)

  and substRegVarComp (dst, newr) (Atom a) = Atom (substRegVarAtom (dst, newr) a)
  | substRegVarComp (dst, newr) (App (m1, m2)) = 
      App (substRegVarAtom (dst, newr) m1, substRegVarAtom (dst, newr) m2)
  | substRegVarComp (dst, newr) (PrimApp (opr, m1, m2)) = 
      PrimApp (opr, substRegVarAtom (dst, newr) m1, substRegVarAtom (dst, newr) m2)
  | substRegVarComp (dst, newr) (First (m)) =
      First (substRegVarAtom (dst, newr) m)
  | substRegVarComp (dst, newr) (Second (m)) =
      Second (substRegVarAtom (dst, newr) m)
  | substRegVarComp (dst, newr) (Unbox m) = 
      Unbox (substRegVarAtom (dst, newr) m)
  | substRegVarComp (dst, newr) (RegionElim (m, r)) = 
      RegionElim (substRegVarAtom (dst, newr) m, r)
  | substRegVarComp (dst, newr) (IfElse (m1, m2, m3)) = 
      IfElse (substRegVarAtom (dst, newr) m1, substRegVar (dst, newr) m2, substRegVar (dst, newr) m3)

  and substRegVar (dst, newr) (Comp c) = Comp (substRegVarComp (dst, newr) c)
  | substRegVar (dst, newr) (Let (x, m1, m2)) = 
      Let (x, substRegVarComp (dst, newr) m1, substRegVar (dst, newr) m2)
  | substRegVar (dst, newr) (LetRegion (r, m)) = 
      LetRegion (r, substRegVar (dst, newr) m)

  and substRegVarValue (dst, newr) (IntLit i) = IntLit i
  | substRegVarValue (dst, newr) (BoolLit b) = BoolLit b
  | substRegVarValue (dst, newr) (UnitLit) = UnitLit
  | substRegVarValue (dst, newr) (Tuple (m1, m2)) = 
      Tuple (substRegVar (dst, newr) m1, substRegVar (dst, newr) m2)
  | substRegVarValue (dst, newr) (BarePointer (r, p)) = (BarePointer (r, p))

  and substRegVarBoxValue (dst, newr) (BoxIntLit (i, r)) = BoxIntLit (i, if dst = r then newr else r)
  | substRegVarBoxValue (dst, newr) (BoxBoolLit (b, r)) = BoxBoolLit (b, if dst = r then newr else r)
  | substRegVarBoxValue (dst, newr) (BoxUnitLit r) = BoxUnitLit (if dst = r then newr else r)
  | substRegVarBoxValue (dst, newr) (BoxAbs a) = BoxAbs (substRegVarAbs (dst, newr) a)
  | substRegVarBoxValue (dst, newr) (BoxTuple (m1, m2, r)) = 
      BoxTuple (substRegVar (dst, newr) m1, substRegVar (dst, newr) m2, if dst = r then newr else r)
  | substRegVarBoxValue (dst, newr) (BoxBarePointer (r1, p, r2)) =
      BoxBarePointer (r1, p, if dst = r2 then newr else r2)

  and substRegVarAbs (dst, newr) (Lambda (x, m, argt, r)) = 
      Lambda (x, substRegVar (dst, newr) m, argt, if dst = r then newr else r)
  | substRegVarAbs (dst, newr) (RegionLambda (r1, m, r2)) = 
      RegionLambda (r1, substRegVarAbs (dst, newr) m, if dst = r2 then newr else r2)

  fun freshvar () = 
    lift M.get >>= (fn (s : int) =>
    lift (M.put (s + 1)) >>= (fn (_ : unit) =>
      return (GenV (s))
    ))

  fun transformTerm (Lang.Value v) = raise Fail ""
  | transformTerm (Lang.BoxedValue v) = raise Fail ""
  | transformTerm (Lang.Var v) = return (Comp (Atom (Var (V v))))
  | transformTerm (Lang.First (m)) = 
      transformAtom m >>= (fn m' => return (Comp (First m')))
  | transformTerm (Lang.Second (m)) = 
      transformAtom m >>= (fn m' => return (Comp (Second m')))
  | transformTerm (Lang.Unbox m) = 
      transformAtom m >>= (fn m' => return (Comp (Unbox m')))
  | transformTerm (Lang.Let (x, m1, m2, argt)) = 
      transformComp m1 >>= (fn m1' => 
      transformTerm m2 >>= (fn m2' => 
        return (Let (V x, m1', m2'))
      ))
  | transformTerm (Lang.LetRegion (r, m)) = 
      transformTerm m >>= (fn t =>
        return (LetRegion (r, t))
      )
  | transformTerm (Lang.RegionElim (m, r1)) = 
      transformAtom m >>= (fn m' => return (Comp (RegionElim (m', r1))))
  | transformTerm (Lang.IfElse (m1, m2, m3)) = 
      transformAtom m1 >>= (fn m1' => 
      transformTerm m2 >>= (fn m2' => 
      transformTerm m3 >>= (fn m3' => 
        return (Comp (IfElse (m1', m2', m3')))
      )))
  | transformTerm (Lang.App (m1, m2)) = 
      transformAtom m1 >>= (fn m1' => 
      transformAtom m2 >>= (fn m2' => 
        return (Comp (App (m1', m2')))
      ))
  | transformTerm (Lang.PrimApp (opr, m1, m2)) = 
      transformAtom m1 >>= (fn m1' => 
      transformAtom m2 >>= (fn m2' => 
        return (Comp (PrimApp (opr, m1', m2')))
      ))

  and transformComp (Lang.Value v) = raise Fail ""
  | transformComp (Lang.BoxedValue v) = raise Fail ""
  | transformComp (Lang.Var v) = return (Atom (Var (V v)))
  | transformComp (Lang.First (m)) = 
      transformAtom m >>= (fn m' => return (First m'))
  | transformComp (Lang.Second (m)) = 
      transformAtom m >>= (fn m' => return (Second m'))
  | transformComp (Lang.Unbox m) = 
      transformAtom m >>= (fn m' => return (Unbox m'))
  | transformComp (Lang.Let (x, m1, m2, argt)) = 
      transformComp m1 >>= (fn m1' => 
      callCC (fn (k : 'a -> 'b monad) =>
      ((transformComp m2) k) >>= (fn (_ : int) => raise Fail "")
        (* return (Let (V x, m1', (transformComp m2) k)) *)
      )) >>= (fn m2'' =>
        raise Fail ""
      )
      (* callCC (fn k =>
        runCont 
      return m2' >>= (fn m2'' =>
        return (fn k => Let (V x, m1', m2''))
      ))) *)
  | transformComp (Lang.LetRegion (r, m)) = 
      transformTerm m >>= (fn t =>
        return (LetRegion (r, t))
      )
  | transformComp (Lang.RegionElim (m, r1)) = 
      transformAtom m >>= (fn m' => return (RegionElim (m', r1)))
  | transformComp (Lang.IfElse (m1, m2, m3)) = 
      transformAtom m1 >>= (fn m1' => 
      transformTerm m2 >>= (fn m2' => 
      transformTerm m3 >>= (fn m3' => 
        return (IfElse (m1', m2', m3'))
      )))
  | transformComp (Lang.App (m1, m2)) = 
      transformAtom m1 >>= (fn m1' => 
      transformAtom m2 >>= (fn m2' => 
        return (App (m1', m2'))
      ))
  | transformComp (Lang.PrimApp (opr, m1, m2)) = 
      transformAtom m1 >>= (fn m1' => 
      transformAtom m2 >>= (fn m2' => 
        return (PrimApp (opr, m1', m2'))
      ))

  and transformAtom m = raise Fail ""
    (* transformComp m >>= (fn (x : comp) => 
      (case x of
        Atom a => return a
      | _ => 
          (* freshvar () >>= (fn t =>
            return (Let (t, x, k (Var t)))
          ) *)
          freshvar () >>= (fn (t : var) =>
          callCC (fn (k : atom monad) => k (Var t)
          ))
      ))
      *)

  (* and transformValue (Lang.IntLit i) = return (IntLit i)
  | transformValue (Lang.BoolLit b) = return (BoolLit b)
  | transformValue (Lang.UnitLit) = return (UnitLit)
  | transformValue (Lang.Tuple (m1, m2)) = 
      transform m1 >>= (fn x =>
      transform m2 >>= (fn y =>
        return (Tuple (x, y))
      ))
  | transformValue (Lang.BarePointer (r, p)) = return (BarePointer (r, p)) *)

  fun isValue (Comp (Atom _)) = true
  | isValue (Comp c) = false
  | isValue (Let (x, m1, m2)) = false
  | isValue (LetRegion (r, m)) = false

end
