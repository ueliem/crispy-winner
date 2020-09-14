structure ClosLangProgram : sig
  type var = ANFTerm.var
  type regionvar = string
  type regionset = RegionSet.regionset
  type effect = RegionSet.effect
  type operator = string

  datatype declaration = 
    DeclType of var * Ty.ty
  | DeclVal of var * Ty.ty * ClosLangTerm.term
  | DeclFun of var * var list * Ty.ty list * Ty.ty * ClosLangTerm.term

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
  | DeclVal of var * Ty.ty * ClosLangTerm.term
  | DeclFun of var * var list * Ty.ty list * Ty.ty * ClosLangTerm.term

  datatype program = 
    Prog of declaration list

end

