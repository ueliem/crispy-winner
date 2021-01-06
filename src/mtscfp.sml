structure MTSCFP : sig
  include CHARPARSER
  val printMsg : string -> unit monad
  val getFileStream : string -> CharFileStream.stream monad 
  val putTokenStream : string -> TokenStream.stream -> unit monad 
  end = struct
  type pos = CharFileStream.pos
  type elem = CharFileStream.item
  type otherErr = unit
  structure CFP = CharFileParser (type e = otherErr; structure Base = MTSCompilerM)
  open CFP
  fun printMsg s = lift (MTSCompilerM.printMsg s)
  fun getFileStream n =
    lift (MTSCompilerM.getFileStream n)
  fun putTokenStream n ts =
    lift (MTSCompilerM.putTokenStream n ts)
end

