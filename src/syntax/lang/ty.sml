structure Ty :
sig
  datatype ty =
    IntTy
  | BoolTy
  | UnitTy
  | TupleTy of ty list
  | FuncTy of RegionSet.regionset * ty list * ty * RegionSet.effect
  | BoxedTy of ty * RegionSet.regionvar
  include TOSTRING where type t = ty
  val eqty : (ty * ty) -> bool
  val substRegVarTy : (RegionSet.regionvar * RegionSet.regionvar) -> ty -> ty
end
=
struct
  datatype ty =
    IntTy
  | BoolTy
  | UnitTy
  | TupleTy of ty list
  | FuncTy of RegionSet.regionset * ty list * ty * RegionSet.effect
  | BoxedTy of ty * RegionSet.regionvar
  type t = ty

  fun eqty (IntTy, IntTy) = true
  | eqty (BoolTy, BoolTy) = true
  | eqty (UnitTy, UnitTy) = true
  | eqty (TupleTy t1, TupleTy t2) =
      List.all (fn x => x = true) (map eqty (ListPair.zipEq (t1, t2)))
  | eqty (FuncTy (rs1, tl1, rt1, phi1), FuncTy (rs2, tl2, rt2, phi2)) =
      List.all (fn x => x = true) (map eqty (ListPair.zipEq (tl1, tl2)))
      andalso eqty (rt1, rt2) andalso Set.eq rs1 rs2 andalso Set.eq phi1 phi2
  | eqty (BoxedTy (t1, r1), BoxedTy (t2, r2)) = eqty (t1, t2) andalso r1 = r2
  | eqty (_, _) = false

  fun substRegVarTy (dst, newr) (IntTy) = IntTy
  | substRegVarTy (dst, newr) (BoolTy) = BoolTy
  | substRegVarTy (dst, newr) (UnitTy) = UnitTy
  | substRegVarTy (dst, newr) (TupleTy t) = 
      TupleTy (map (substRegVarTy (dst, newr)) t)
  | substRegVarTy (dst, newr) (FuncTy (rvl, t1, t2, phi)) =
      FuncTy (rvl, map (substRegVarTy (dst, newr)) t1, 
        substRegVarTy (dst, newr) t2,
        Set.map (fn r => if dst = r then newr else r) phi)
  | substRegVarTy (dst, newr) (BoxedTy (t, r)) = 
      BoxedTy (substRegVarTy (dst, newr) t, if dst = r then newr else r)

  fun tostring (IntTy) = "int"
  | tostring (BoolTy) = "bool"
  | tostring (UnitTy) = "unit"
  | tostring (TupleTy tl) =
      String.concat ["(", String.concatWith ", " (map tostring tl), ")"]
  | tostring (FuncTy (rs, argt, rt, phi)) =
      String.concat ["forall ", RegionSet.tostring rs,
        "(", String.concatWith ", " (map tostring argt), ") -> ",
        RegionSet.tostring phi, " ", tostring rt]
  | tostring (BoxedTy (t, r)) = String.concat [tostring t, " at ", r]

end

