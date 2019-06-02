signature SET =
sig
  type ''a set
  val emptyset : ''a set
  val member : ''a -> ''a set -> bool
  val isempty : ''a set -> bool
  val size : ''a set -> int
  val insert : ''a -> ''a set -> ''a set
  val remove : ''a -> ''a set -> ''a set

  val union : ''a set -> ''a set -> ''a set
  (* val intersection : ''a set -> ''a set -> ''a set *)
  val difference : ''a set -> ''a set -> ''a set
  (* val subset : ''a set -> ''a set -> ''a set*)
end

structure Set : SET =
struct
  type ''a set = ''a list

  val emptyset = []

  fun member i s =
    List.exists (fn x => x = i) s

  fun isempty s = List.null s

  fun size s = List.length s

  fun insert i s =
    if not (member i s) then i::s
    else s

  fun remove i [] = []
  | remove i (x::xs) =
      if i = x then xs
      else x::xs

  fun union s t =
    List.filter (fn x => not (member x t)) s @ t

  fun difference s t =
    List.filter (fn x => not (member x t)) s

end

