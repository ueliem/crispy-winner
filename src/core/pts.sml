structure PTS : sig

  datatype var =
    Var of int
  | Anonymous

  datatype Lit =
    IntType
  | IntLit of int
  | BoolLit of bool
  | BoolType

  datatype term =
    Sort of FuncSpec.sort
  | Variable of int
  | Literal of Lit
  | Abs of term * term
  | App of term * term
  | DepProd of term * term
  | LetTerm of term * term * term
  | DepSum of term * term
  | DepPair of term * term * term
  | Fst of term
  | Snd of term
  | Unknown

  type env = term list
  type defs = (int * term, term) AssocList.asl

  val update : int -> int -> term -> term
  val subst : int -> term -> term -> term
  val whstep : defs -> term -> term option
  val whreduce : defs -> term -> term
  val nfstep : defs -> term -> term option
  val nfreduce : defs -> term -> term

end
=
struct
  open OptionMonad

  datatype var =
    Var of int
  | Anonymous

  datatype Lit =
    IntType
  | IntLit of int
  | BoolLit of bool
  | BoolType

  datatype term =
    Sort of FuncSpec.sort
  | Variable of int
  | Literal of Lit
  | Abs of term * term
  | App of term * term
  | DepProd of term * term
  | LetTerm of term * term * term
  | DepSum of term * term
  | DepPair of term * term * term
  | Fst of term
  | Snd of term
  | Unknown

  type env = term list
  type defs = (int * term, term) AssocList.asl

  fun update k i t =
    case t of
      Sort _ => t
    | Variable (n) =>
        if n > k then Variable (n + i - 1)
        else Variable (n)
    | Literal _ => t
    | Abs (t1, t2) => 
        Abs (update k i t1, update (k + 1) i t2)
    | App (t1, t2) => 
        App (update k i t1, update k i t2)
    | DepProd (t1, t2) => 
        DepProd (update k i t1, update (k + 1) i t2)
    | LetTerm (t1, t2, t3) => 
        LetTerm (update k i t1, update k i t2, update (k + 1) i t3)
    | DepSum (t1, t2) => DepSum (update k i t1, update (k + 1) i t2)
    | DepPair (t1, t2, t3) => DepPair (update k i t1, update k i t2, update k i t3)
    | Fst (t1) => Fst (update k i t1)
    | Snd (t1) => Snd (update k i t1)
    | Unknown => t

  fun subst i s t =
    case t of
      Sort _ => t
    | Variable (n) =>
        if n > i then Variable (n - 1)
        else if n = i then update 0 i s
        else Variable (n)
    | Literal _ => t
    | Abs (t1, t2) => 
        Abs (subst i s t1, subst (i + 1) s t2)
    | App (t1, t2) => 
        App (subst i s t1, subst i s t1)
    | DepProd (t1, t2) => 
        DepProd (subst i s t1, subst (i + 1) s t2)
    | LetTerm (t1, t2, t3) => 
        LetTerm (subst i s t1, subst i s t2, subst (i + 1) s t3)
    | DepSum (t1, t2) => DepSum (subst i s t1, subst i s t2)
    | DepPair (t1, t2, t3) => DepPair (subst i s t1, subst i s t2, subst i s t3)
    | Fst (t1) => Fst (subst i s t1)
    | Snd (t1) => Snd (subst i s t1)
    | Unknown => t

  fun whstep delta Unknown = zero
  | whstep delta (Variable (n)) = zero
  | whstep delta (Sort _) = zero
  | whstep delta (Literal _) = zero
  | whstep delta (App (Abs (t1, t2), t3)) = 
      return (subst 1 t3 t2)
  | whstep delta (App (t1, t2)) = 
      (case whstep delta t1 of
        SOME t1' => whstep delta (App (t1', t2)) ++ return (App (t1', t2))
      | NONE => zero)
  | whstep delta (Abs (t1, t2)) = zero
  | whstep delta (DepProd (t1, t2)) = zero
  | whstep delta (LetTerm (t1, t2, t3)) = 
      return (subst 1 t3 t2)
  | whstep delta (DepSum (t1, t2)) = zero
  | whstep delta (DepPair (t1, t2, t3)) = zero
  | whstep delta (Fst (t1)) = 
      (case whstep delta t1 of
        SOME (DepPair (t2, t3, t4)) => return t2
      | SOME t1' => whstep delta (Fst (t1')) ++ return (Fst (t1'))
      | NONE => zero)
  | whstep delta (Snd (t1)) = 
      (case whstep delta t1 of
        SOME (DepPair (t2, t3, t4)) => return t3
      | SOME t1' => whstep delta (Snd (t1')) ++ return (Snd (t1'))
      | NONE => zero)

  fun whreduce delta x =
    case whstep delta x of
      SOME x' => whreduce delta x'
    | NONE => x

  fun nfstep delta Unknown = zero
  | nfstep delta (Variable (n)) = zero
  | nfstep delta (Sort s) = zero
  | nfstep delta (Literal l) = zero
  | nfstep delta (App (Abs (t1, t2), t3)) =
      let val t2' = subst 1 t3 t2
      in
        nfstep delta t2' ++ return t2'
      end
  | nfstep delta (App (t1, t2)) =
      nfstep delta t1 >>= (fn t1' =>
        nfstep delta (App (t1', t2)) ++ return (App (t1', t2))
      )
      ++ nfstep delta t2 >>= (fn t2' =>
        nfstep delta (App (t1, t2')) ++ return (App (t1, t2'))
      )
      ++ zero
  | nfstep delta (Abs (t1, t2)) = 
      (case (nfstep delta t1, nfstep delta t2) of
        (NONE, NONE) => zero
      | (SOME t1', NONE) => return (Abs (t1', t2))
      | (NONE, SOME t2') => return (Abs (t1, t2'))
      | (SOME t1', SOME t2') => return (Abs (t1', t2'))
      )
  | nfstep delta (DepProd (t1, t2)) = zero
  | nfstep delta (LetTerm (t1, t2, t3)) =
      let val t3' = subst 1 t2 t3
      in
        nfstep delta t3' ++ return t3'
      end
  | nfstep delta (DepSum (t1, t2)) = zero
  | nfstep delta (DepPair (t1, t2, t3)) = zero
  | nfstep delta (Fst (t1)) = 
      (case nfstep delta t1 of
        SOME (DepPair (t2, t3, t4)) => return t2
      | SOME t1' => nfstep delta (Fst (t1')) ++ return (Fst (t1'))
      | NONE => zero)
  | nfstep delta (Snd (t1)) = 
      (case nfstep delta t1 of
        SOME (DepPair (t2, t3, t4)) => return t3
      | SOME t1' => nfstep delta (Snd (t1')) ++ return (Snd (t1'))
      | NONE => zero)

  fun nfreduce delta x =
    case nfstep delta x of
      SOME x' => nfreduce delta x'
    | NONE => x

end

