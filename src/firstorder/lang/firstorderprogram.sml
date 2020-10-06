structure FirstOrderProgram : sig
  type var = ANFTerm.var
  type regionvar = string
  type regionset = RegionSet.regionset
  type effect = RegionSet.effect
  type operator = string

  datatype declaration = 
    DeclType of var * Ty.ty
  | DeclVal of var * Ty.ty * FirstOrderTerm.term
  | DeclFun of var * var list * Ty.ty list * Ty.ty * FirstOrderTerm.term

  datatype program =
    Prog of declaration list

end
=
struct
  type var = ANFTerm.var
  type regionvar = string
  type regionset = RegionSet.regionset
  type effect = RegionSet.effect
  type operator = string

  datatype declaration = 
    DeclType of var * Ty.ty
  | DeclVal of var * Ty.ty * FirstOrderTerm.term
  | DeclFun of var * var list * Ty.ty list * Ty.ty * FirstOrderTerm.term

  datatype program = 
    Prog of declaration list

end

