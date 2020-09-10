structure SSA :
sig
  type var = int
  type label = string
  type phinode = string
  type operator = string
  datatype atom =
    Var of var
  | Const of int
  datatype expr =
    Atom of atom
  | Call
  | PrimApp of operator * atom list
  
  type block = label * phinode list * stmt

  datatype stmt =
    Assign of var * expr * block
  | GoTo of label
  | IfElse of expr * block * block
  | Return of expr
end
=
struct
end

