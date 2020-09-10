structure RegionSet :
sig
  type regionvar = string
  type regionset = regionvar Set.set
  type effect = regionvar Set.set
  include TOSTRING where type t = regionset

  val substRegVarRegSet : (regionvar * regionvar) -> regionset -> regionset

end
=
struct
  type regionvar = string
  type regionset = regionvar Set.set
  type effect = regionvar Set.set
  type t = regionset

  fun substRegVarRegSet (dst, newr) rs =
    Set.map (fn x => if x = dst then newr else x) rs

  fun tostring rs =
    String.concat ["{", (String.concatWith ", " (Set.toList rs)), "}"]
end

