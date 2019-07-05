structure Syntax : sig
  datatype sort =
    Kind
  | ProperType
  | IntSort
  | BoolSort
  type sorts = sort list
  type axiom = sort * sort
  type axioms = axiom list
  type rule = sort * sort * sort
  type rules = rule list

  type spec = sorts * axioms * rules

  datatype var =
    Anonymous
  | Var of string
  | RenamedVar of int * string

  datatype lit =
    IntType
  | IntLit of int
  | BoolType
  | BoolLit of bool

  datatype term =
    Sort of sort
  | Variable of var
  | Literal of lit
  | Abs of var * term * term
  | App of term * term
  | DepProd of var * term * term
  | Unknown
  | PrimApp of string * term * term
  | LetTerm of var * term * term * term
  | DepSum of var * term * term
  | Pair of term * term
  | Fst of term
  | Snd of term
  | FuncType of term * term

  datatype declaration =
    Value of var * term * term

  datatype program = Prog of declaration list

  val weak_subst : string -> term -> term -> term
  val weak_replace : string -> var -> term -> term
  val weak_replace_decl : string -> var -> declaration -> declaration
  (* val strong_subst : string -> term -> term -> term *)

end
=
struct
  open OptionMonad

  datatype sort =
    Kind
  | ProperType
  | IntSort
  | BoolSort

  type sorts = sort list
  type axiom = sort * sort
  type axioms = axiom list
  type rule = sort * sort * sort
  type rules = rule list

  type spec = sorts * axioms * rules

  datatype var =
    Anonymous
  | Var of string
  | RenamedVar of int * string

  datatype lit =
    IntType
  | IntLit of int
  | BoolType
  | BoolLit of bool

  datatype term =
    Sort of sort
  | Variable of var
  | Literal of lit
  | Abs of var * term * term
  | App of term * term
  | DepProd of var * term * term
  | Unknown
  | PrimApp of string * term * term
  | LetTerm of var * term * term * term
  | DepSum of var * term * term
  | Pair of term * term
  | Fst of term
  | Snd of term
  | FuncType of term * term

  datatype declaration =
    Value of var * term * term

  datatype program = Prog of declaration list

  fun weak_subst v t1 t2 =
    case t2 of
      Sort _ => t2
    | Variable (x) => 
        (case x of
          Anonymous => Variable (Anonymous)
        | Var y => 
            if y = v then t1
            else Variable (x)
        | RenamedVar _ => Variable (x))
    | Literal _ => t2
    | Abs (x, t3, t4) =>
        (case x of
          Anonymous => Abs (Anonymous, weak_subst v t1 t3, weak_subst v t1 t4)
        | Var y => 
            if y = v then t2
            else Abs (x, weak_subst v t1 t3, weak_subst v t1 t4)
        | RenamedVar _ => Abs (x, weak_subst v t1 t3, weak_subst v t1 t4))
    | App (t3, t4) => App (weak_subst v t1 t3, weak_subst v t1 t4)
    | DepProd (x, t3, t4) =>
        (case x of
          Anonymous => DepProd (Anonymous, weak_subst v t1 t3, weak_subst v t1 t4)
        | Var y => 
            if y = v then t2
            else DepProd (x, weak_subst v t1 t3, weak_subst v t1 t4)
        | RenamedVar _ => DepProd (x, weak_subst v t1 t3, weak_subst v t1 t4))
    | Unknown => t2
    | PrimApp (b, t3, t4) => PrimApp (b, weak_subst v t1 t3, weak_subst v t1 t4)
    | LetTerm (x, t3, t4, t5) => 
        (case x of
          Anonymous => 
            LetTerm (Anonymous, weak_subst v t1 t3, weak_subst v t1 t4, weak_subst v t1 t5)
        | Var y => 
            if y = v then t2
            else LetTerm (x, weak_subst v t1 t3, weak_subst v t1 t4, weak_subst v t1 t5)
        | RenamedVar _ => LetTerm (x, weak_subst v t1 t3, weak_subst v t1 t4, weak_subst v t1 t5))
    | DepSum (x, t3, t4) => 
        (case x of
          Anonymous => DepSum (Anonymous, weak_subst v t1 t3, weak_subst v t1 t4)
        | Var y => 
            if y = v then t2
            else DepSum (x, weak_subst v t1 t3, weak_subst v t1 t4)
        | RenamedVar _ => DepSum (x, weak_subst v t1 t3, weak_subst v t1 t4))
    | Pair (t3, t4) => Pair (weak_subst v t1 t3, weak_subst v t1 t4)
    | Fst t3 => Fst (weak_subst v t1 t3)
    | Snd t3 => Snd (weak_subst v t1 t3)
    | FuncType (t3, t4) => FuncType (weak_subst v t1 t3, weak_subst v t1 t4)

  fun weak_replace v u t1 =
    case t1 of
      Sort _ => t1
    | Variable (x) => 
        (case x of
          Anonymous => Variable (Anonymous)
        | Var y => 
            if y = v then Variable (u)
            else Variable (x)
        | RenamedVar _ => Variable (x))
    | Literal _ => t1
    | Abs (x, t2, t3) =>
        (case x of
          Anonymous => Abs (Anonymous, weak_replace v u t2, weak_replace v u t3)
        | Var y => 
            if y = v then t1
            else Abs (x, weak_replace v u t2, weak_replace v u t3)
        | RenamedVar _ => Abs (x, weak_replace v u t2, weak_replace v u t3))
    | App (t2, t3) => App (weak_replace v u t2, weak_replace v u t3)
    | DepProd (x, t2, t3) =>
        (case x of
          Anonymous => DepProd (Anonymous, weak_replace v u t2, weak_replace v u t3)
        | Var y => 
            if y = v then t1
            else DepProd (x, weak_replace v u t2, weak_replace v u t3)
        | RenamedVar _ => DepProd (x, weak_replace v u t2, weak_replace v u t3))
    | Unknown => t1
    | PrimApp (b, t2, t3) => PrimApp (b, weak_replace v u t2, weak_replace v u t3)
    | LetTerm (x, t2, t3, t4) => 
        (case x of
          Anonymous => 
            LetTerm (Anonymous, weak_replace v u t2, weak_replace v u t3, weak_replace v u t4)
        | Var y => 
            if y = v then t1
            else LetTerm (x, weak_replace v u t2, weak_replace v u t3, weak_replace v u t4)
        | RenamedVar _ => LetTerm (x, weak_replace v u t2, weak_replace v u t3, weak_replace v u t4))
    | DepSum (x, t2, t3) => 
        (case x of
          Anonymous => DepSum (Anonymous, weak_replace v u t2, weak_replace v u t3)
        | Var y => 
            if y = v then t1
            else DepSum (x, weak_replace v u t2, weak_replace v u t3)
        | RenamedVar _ => DepSum (x, weak_replace v u t2, weak_replace v u t3))
    | Pair (t2, t3) => Pair (weak_replace v u t2, weak_replace v u t3)
    | Fst t2 => Fst (weak_replace v u t2)
    | Snd t2 => Snd (weak_replace v u t2)
    | FuncType (t2, t3) => FuncType (weak_replace v u t2, weak_replace v u t3)

  fun weak_replace_decl v u t =
    case t of
      Value (x, t1, t2) => 
        (case x of
          Anonymous => raise Fail "makes no sense"
        | Var y => 
            if y = v then 
              Value (u, weak_replace v u t1, weak_replace v u t2)
            else
              Value (x, weak_replace v u t1, weak_replace v u t2)
        | RenamedVar _ =>
            Value (x, weak_replace v u t1, weak_replace v u t2)
        )

end

