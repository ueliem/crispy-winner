structure MTS :
sig
  type name = string
  datatype var =
    NamedVar of name
  | GenVar of int
  | IndexVar of int * name
  | AnonVar
  datatype sort =
    TypeVal
  | KindVal
  | TypeComp
  | KindComp
  type sorts = sort list
  type ax = (sort * sort) list
  type rules = (sort * sort * sort) list
  datatype iop =
    IOpAdd
  | IOpSub
  | IOpMul
  | IOpDiv
  | IOpGT
  | IOpGE
  | IOpLT
  | IOpLE
  datatype bop =
    BOpAnd
  | BOpOr
  | BOpXOr
  | BOpNot
  datatype operator =
    OpInt of iop
  | OpBool of bop
  | OpSelect of int
  datatype lit =
    IntLit of int
  | BoolLit of bool
  | IntTyLit
  | BoolTyLit
  datatype pattern =
    PatLit of lit
  | PatVar of name
  | PatTuple of pattern * pattern
  | PatCons of name * pattern list
  datatype term =
    Var of var
  | Lit of lit
  | Sort of sort
  | App of term * term
  | Case of term * (pattern * term) list * term
  | IfElse of term * term * term
  | Let of var * term * term * term
  | Lambda of var * term * term
  | DepProduct of var * term * term
  | DepSum of var * term * term
  | Tuple of term * term * term
  | First of term
  | Second of term
  type valdef = var * term * term
  type datadef = name * term * (name * term) list
  type newtydef = name * term * name * term
  type classdef = name * (name * term) list
  type instancedef = name * name * (name * term) list
  datatype def =
    DefVal of valdef
  | DefData of datadef
  | DefNewTy of newtydef
  | DefClass of classdef
  | DefInstance of instancedef

  val eqv : var -> var -> bool
  val eq : term -> term -> bool

end
=
struct
  type name = string
  datatype var =
    NamedVar of name
  | GenVar of int
  | IndexVar of int * name
  | AnonVar
  datatype sort =
    TypeVal
  | KindVal
  | TypeComp
  | KindComp
  type sorts = sort list
  type ax = (sort * sort) list
  type rules = (sort * sort * sort) list
  datatype iop =
    IOpAdd
  | IOpSub
  | IOpMul
  | IOpDiv
  | IOpGT
  | IOpGE
  | IOpLT
  | IOpLE
  datatype bop =
    BOpAnd
  | BOpOr
  | BOpXOr
  | BOpNot
  datatype operator =
    OpInt of iop
  | OpBool of bop
  | OpSelect of int
  datatype lit =
    IntLit of int
  | BoolLit of bool
  | IntTyLit
  | BoolTyLit
  datatype pattern =
    PatLit of lit
  | PatVar of name
  | PatTuple of pattern * pattern
  | PatCons of name * pattern list
  datatype term =
    Var of var
  | Lit of lit
  | Sort of sort
  | App of term * term
  | Case of term * (pattern * term) list * term
  | IfElse of term * term * term
  | Let of var * term * term * term
  | Lambda of var * term * term
  | DepProduct of var * term * term
  | DepSum of var * term * term
  | Tuple of term * term * term
  | First of term
  | Second of term
  type valdef = var * term * term
  type datadef = name * term * (name * term) list
  type newtydef = name * term * name * term
  type classdef = name * (name * term) list
  type instancedef = name * name * (name * term) list
  datatype def =
    DefVal of valdef
  | DefData of datadef
  | DefNewTy of newtydef
  | DefClass of classdef
  | DefInstance of instancedef

  fun eqv (NamedVar n) (NamedVar n') = n = n'
  | eqv (IndexVar (i, _)) (IndexVar (i', _)) = i = i'
  | eqv _ _ = raise Fail "gotta think on this"

  fun eq (Var v) (Var v') = eqv v v'
  | eq (Lit l) (Lit l') = l = l'
  | eq (Sort s) (Sort s') = s = s'
  | eq (App (m1, m2)) (App (m1', m2')) =
      eq m1 m1' andalso eq m2 m2'
  | eq (IfElse (m1, m2, m3)) (IfElse (m1', m2', m3')) =
      eq m1 m1' andalso eq m2 m2' andalso eq m3 m3'
  | eq (Let (v, m1, m2, m3)) (Let (v', m1', m2', m3')) =
      eqv v v' andalso eq m1 m1' andalso eq m2 m2'
  | eq (Lambda (v, m1, m2)) (Lambda (v', m1', m2')) =
      eqv v v' andalso eq m1 m1' andalso eq m2 m2'
  | eq (DepProduct (v, m1, m2)) (DepProduct (v', m1', m2')) =
      eqv v v' andalso eq m1 m1' andalso eq m2 m2'
  | eq _ _ = false

end

