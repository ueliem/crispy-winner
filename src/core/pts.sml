structure PTS : sig
  type vname
  type tyname

  datatype sort =
    ProperTypes
  | Kinds
  | IntSort
  | BoolSort

  type sorts = sort list
  type axiom = sort * sort
  type axioms = axiom list
  type rule = sort * sort * sort
  type rules = rule list

  type spec = sorts * axioms * rules

  datatype Lit =
    IntType
  | IntLit of int

  datatype term =
    Sort of sort
  | Variable of vname * term
  | Literal of Lit
  | Abs of vname * term * term
  | App of term * term
  | DepProd of vname * term * term
  | Unknown

  val minus : spec -> sort option -> sort option
  val plus : spec -> sort option -> sort option
  val rho : spec -> (sort option * sort option) -> sort option
  val mu : spec -> (sort option * sort option) -> sort option
  val sort : spec -> (vname, term) AssocList.asl -> term option -> sort option
  val elmt : spec -> (vname, term) AssocList.asl -> term option -> sort option
  val freevars : term -> vname Set.set
  val weaksubst : (vname * term) -> term -> term
  val strongsubst : (vname * term) -> term -> term
  val whstep : term -> term option
  val whreduce : term -> term
  val nfstep : term -> term option
  val nfreduce : term -> term
  val evalstep : term -> term option
  val eval : term -> term
end
=
struct
  open OptionMonad
  type vname = string
  type tyname = string

  datatype sort =
    ProperTypes
  | Kinds
  type sorts = sort list
  type axiom = sort * sort
  type axioms = axiom list
  type rule = sort * sort * sort
  type rules = rule list

  type spec = sorts * axioms * rules

  datatype Lit =
    IntType
  | IntLit of int

  datatype term =
    Sort of sort
  | Variable of vname * term
  | Literal of Lit
  | Abs of vname * term * term
  | App of term * term
  | DepProd of vname * term * term
  | Unknown

  fun minus sp s =
    case s of
      SOME t =>
        (case List.find (fn x => #2 x = t) (#2 sp) of
          SOME pair => SOME (#1 pair)
        | NONE => NONE
        )
    | NONE => NONE

  fun plus sp s =
    case s of
      SOME t =>
        (case List.find (fn x => #1 x = t) (#2 sp) of
          SOME pair => SOME (#2 pair)
        | NONE => NONE
        )
    | NONE => NONE

  fun rho sp (SOME t1, SOME t2) =
    (case List.find (fn x => #1 x = t1 andalso #2 x = t2) (#3 sp) of
      SOME triple => SOME (#3 triple)
    | NONE => NONE
    )
  | rho sp (SOME t1, NONE) = NONE
  | rho sp (NONE, SOME t2) = NONE
  | rho sp (NONE, NONE) = NONE

  fun mu sp (SOME t1, SOME t2) =
    (case List.find (fn x => (#1 x) = t1 andalso (#3 x) = t2) (#3 sp) of
      SOME triple => SOME (#2 triple)
    | NONE => NONE
    )
  | mu sp (SOME t1, NONE) = NONE
  | mu sp (NONE, SOME t2) = NONE
  | mu sp (NONE, NONE) = NONE

  fun sort sp env t =
    (case t of
      SOME t' => 
        (case t' of
          Unknown => NONE
        | (Variable (v, t1)) => minus sp (elmt sp env (SOME (Variable (v, t1))))
        | (Literal l) =>
            (case l of
              IntType => SOME ProperTypes
            | IntLit i => SOME IntSort
            )
        | (Sort s) => plus sp (SOME s)
        | (App (t1, t2)) => minus sp (elmt sp env (SOME (App (t1, t2))))
        | (Abs (v, t1, t2)) => minus sp (elmt sp env (SOME (Abs (v, t1, t2))))
        | (DepProd (v, t1, t2)) => 
            rho sp (sort sp env (SOME t1), elmt sp (AssocList.insert (v, t1) env) (SOME t2))
        )
    | NONE => NONE)
  and elmt sp env t =
    (case t of
      SOME t' => 
        (case t' of
          Unknown => NONE
        | (Variable (v, t1)) => sort sp env (SOME t1)
        | (Literal l) =>
            (case l of
              IntType => SOME Kinds
            | IntLit i => SOME ProperTypes
            )
        | (Sort s) => plus sp (plus sp (SOME s))
        | (App (t1, t2)) => mu sp (elmt sp env (SOME t1), elmt sp env (SOME t2))
        | (Abs (v, t1, t2)) => 
            rho sp (sort sp env (SOME t1), elmt sp (AssocList.insert (v, t1) env) (SOME t2))
        | (DepProd (v, t1, t2)) => plus sp (sort sp env (SOME (DepProd (v, t1, t2))))
        )
    | NONE => NONE)

  fun weaksubst (x, y) Unknown = Unknown
  | weaksubst (x, y) (Variable (v, t1)) = 
      if v = x then y else Variable (v, weaksubst (x, y) t1)
  | weaksubst (x, y) (Literal l) = Literal l
  | weaksubst (x, y) (Sort s) = (Sort s)
  | weaksubst (x, y) (App (t1, t2)) = App (weaksubst (x, y) t1, weaksubst (x, y) t2)
  | weaksubst (x, y) (Abs (v, t1, t2)) = 
      if v = x then Abs (v, t1, t2) else Abs (v, weaksubst (x, y) t1, weaksubst (x, y) t2)
  | weaksubst (x, y) (DepProd (v, t1, t2)) =
      if v = x then DepProd (v, t1, t2) else DepProd (v, weaksubst (x, y) t1, weaksubst (x, y) t2)

  fun freevars (Unknown) = Set.emptyset
  | freevars (Variable (v, t1)) = Set.union [v] (freevars t1)
  | freevars (Sort s) = Set.emptyset
  | freevars (Literal l) = Set.emptyset
  | freevars (App (t1, t2)) = Set.union (freevars t1) (freevars t2)
  | freevars (Abs (v, t1, t2)) = 
      Set.remove v (Set.union (freevars t1) (freevars t2))
  | freevars (DepProd (v, t1, t2)) =
      Set.remove v (Set.union (freevars t1) (freevars t2))

  fun strongsubst (x, y) Unknown = Unknown
  | strongsubst (x, y) (Variable (v, t1)) = 
      if v = x then y else Variable (v, strongsubst (x, y) t1)
  | strongsubst (x, y) (Literal l) = Literal l
  | strongsubst (x, y) (Sort s) = (Sort s)
  | strongsubst (x, y) (App (t1, t2)) = App (strongsubst (x, y) t1, strongsubst (x, y) t2)
  | strongsubst (x, y) (Abs (v, t1, t2)) = 
      if v = x then Abs (v, t1, t2) else Abs (v, strongsubst (x, y) t1, strongsubst (x, y) t2)
  | strongsubst (x, y) (DepProd (v, t1, t2)) =
      if v = x then DepProd (v, t1, t2) else DepProd (v, strongsubst (x, y) t1, strongsubst (x, y) t2)

  fun whstep Unknown = zero
  | whstep (Variable (v, t1)) = zero
  | whstep (Sort s) = zero
  | whstep (Literal l) = zero
  | whstep (App (Abs (v, t1, t2), t3)) = 
      return (weaksubst (v, t3) t2)
  | whstep (App (t1, t2)) = 
      (case whstep t1 of
        SOME t1' => whstep (App (t1', t2)) ++ return (App (t1', t2))
      | NONE => zero)
  | whstep (Abs (v, t1, t2)) = zero
  | whstep (DepProd (v, t1, t2)) = zero

  fun whreduce x =
    case whstep x of
      SOME x' => whreduce x'
    | NONE => x

  fun nfstep Unknown = zero
  | nfstep (Variable (v, t1)) = zero
  | nfstep (Sort s) = zero
  | nfstep (Literal l) = zero
  | nfstep (App (Abs (v, t1, t2), t3)) =
      let val a' = strongsubst (v, t3) t2
      in
        nfstep a' ++ return a'
      end
  | nfstep (App (t1, t2)) =
      nfstep t1 >>= (fn t1' =>
        nfstep (App (t1', t2)) ++ return (App (t1', t2))
      )
      ++ nfstep t2 >>= (fn t2' =>
        nfstep (App (t1, t2')) ++ return (App (t1, t2'))
      )
      ++ zero
  | nfstep (Abs (v, t1, t2)) = 
      (case (nfstep t1, nfstep t2) of
        (NONE, NONE) => zero
      | (SOME t1', NONE) => return (Abs (v, t1', t2))
      | (NONE, SOME t2') => return (Abs (v, t1, t2'))
      | (SOME t1', SOME t2') => return (Abs (v, t1', t2'))
      )
  | nfstep (DepProd (v, t1, t2)) = zero

  fun nfreduce x =
    case nfstep x of
      SOME x' => nfreduce x'
    | NONE => x

  fun evalstep Unknown = zero
  | evalstep (Variable (v, t1)) = zero
  | evalstep (Sort s) = zero
  | evalstep (Literal l) = zero
  | evalstep (App (Abs (v, t1, t2), t3)) =
      return (weaksubst (v, t3) t2)
  | evalstep (App (t1, t2)) =
      evalstep t1 >>= (fn t1' =>
        evalstep (App (t1', t2)) ++ return (App (t1', t2))
      )
      ++ evalstep t2 >>= (fn t2' =>
        evalstep (App (t1, t2')) ++ return (App (t1, t2'))
      )
      ++ zero
  | evalstep (Abs (v, t1, t2)) = zero
  | evalstep (DepProd (v, t1, t2)) = zero

  fun eval x =
    case evalstep x of
      SOME x' => eval x'
    | NONE => x

end

