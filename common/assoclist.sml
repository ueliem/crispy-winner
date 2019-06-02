structure AssocList : sig
  type (''key, 'value) asl

  val ismember : ''key -> (''key, 'value) asl -> bool
  val insert : (''key * 'value) -> (''key, 'value) asl -> (''key, 'value) asl
  val get : ''key -> (''key, 'value) asl -> 'value option
end
=
struct
  type (''key, 'value) asl = (''key * 'value) list

  fun ismember k l =
    List.exists (fn (x, y) => x = k) l

  fun insert (k, v) l =
    if ismember k l then raise Fail "key already exists"
    else (k, v)::l

  fun get k l =
    case (List.find (fn (x, y) => x = k) l) of
      SOME (x, t) => SOME t
    | NONE => NONE
end

