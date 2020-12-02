signature TOSTRING =
sig
  type t
  val tostring : t -> string
end

datatype ('a, 'b) either =
  Left of 'a
| Right of 'b

