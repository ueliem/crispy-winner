structure FirstOrderProgram : sig
  type var = FirstOrderTerm.var
  type regionvar = string
  type regionset = RegionSet.regionset
  type effect = RegionSet.effect
  type operator = string

  datatype declaration = 
    DeclType of var * Ty.ty
  | DeclVal of var * Ty.ty * Term.term
  | DeclFun of var * Ty.ty list * Ty.ty * Term.term

  datatype program = 
    Prog of declaration list

end
=
struct
  type var = FirstOrderTerm.var
  type regionvar = string
  type regionset = RegionSet.regionset
  type effect = RegionSet.effect
  type operator = string

  datatype declaration = 
    DeclType of var * Ty.ty
  | DeclVal of var * Ty.ty * Term.term
  | DeclFun of var * Ty.ty list * Ty.ty * Term.term

  datatype program = 
    Prog of declaration list

end

