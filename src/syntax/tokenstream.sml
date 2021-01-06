structure TokenStream : sig
  include STREAM where type item = TokenVector.item
  val emptyStream : stream
  val fromList : item list -> stream
end = struct
  structure TS = MonoVectorStream (structure S = TokenVector;
    val eq = (fn (x, y) => x = y);
    val stringOfPos = (fn p => Int.toString p);
    val stringOfElem = (fn (p, t) => MTSToken.stringOf t))
  open TS
  val emptyStream = ({ pos = 0, s = (TokenVector.fromList []) })
  fun fromList l = { s = (TokenVector.fromList l), pos = 0 }
end
