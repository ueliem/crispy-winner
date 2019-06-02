structure Syntax : sig
  datatype sort =
    ProperTypes
  | Kinds
  type sorts = sort list
  type axiom = sort * sort
  type axioms = axiom list
  type rule = sort * sort * sort
  type rules = rule list

  type spec = sorts * axioms * rules

  datatype var =
    Anonymous
  | Var of string

  datatype lit =
    IntType
  | IntLit of int

  datatype term =
    Sort of sort
  | Variable of var * term
  | Literal of lit
  | Abs of var * term * term
  | App of term * term
  | DepProd of var * term * term
  | Unknown
  | PrimApp of string * term * term
  | LetTerm of var * term * term
  | DepSum of var * term * term
  | Pair of term * term
  | Fst of term
  | Snd of term
  | FuncType of term * term

  datatype Declaration =
    Value of var * term * term

  datatype program = Prog of Declaration list

end
=
struct
  open OptionMonad

  datatype sort =
    ProperTypes
  | Kinds
  type sorts = sort list
  type axiom = sort * sort
  type axioms = axiom list
  type rule = sort * sort * sort
  type rules = rule list

  type spec = sorts * axioms * rules

  datatype var =
    Anonymous
  | Var of string

  datatype lit =
    IntType
  | IntLit of int

  datatype term =
    Sort of sort
  | Variable of var * term
  | Literal of lit
  | Abs of var * term * term
  | App of term * term
  | DepProd of var * term * term
  | Unknown
  | PrimApp of string * term * term
  | LetTerm of var * term * term
  | DepSum of var * term * term
  | Pair of term * term
  | Fst of term
  | Snd of term
  | FuncType of term * term

  datatype Declaration =
    Value of var * term * term

  datatype program = Prog of Declaration list

end

