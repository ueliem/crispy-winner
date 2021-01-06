signature PARSERERR = sig
  type e
  structure S : STREAM
  type s = S.stream
  type pos = S.pos
  type elem = S.item
  datatype info =
    InfoToken of elem
  | InfoMessage of string
  datatype singleErr =
    Message of string
  | Expected of info
  | Unexpected of info
  | Other of e
  type err = S.pos * singleErr list
  val error : pos -> singleErr list -> err
  val unexpectedEOI : singleErr
  val expectedEOI : singleErr
  val emptyError : pos -> err
  val addError : err -> singleErr -> err
  val merge : err -> err -> err
  val stringOfInfo : info -> string
  val stringOfErrors : singleErr list -> string
end

functor ParserErrT (type e; structure S : STREAM) : PARSERERR = struct
  type e = e
  structure S = S
  type s = S.stream
  type pos = S.pos
  type elem = S.item
  datatype info =
    InfoToken of elem
  | InfoMessage of string
  datatype singleErr =
    Message of string
  | Expected of info
  | Unexpected of info
  | Other of e
  type err = S.pos * singleErr list

  fun error p rs = (p, rs)
  val unexpectedEOI = Unexpected (InfoMessage "EOI")
  val expectedEOI = Expected (InfoMessage "EOI")
  fun emptyError p = (p, [])
  fun addError (p, rs) r  = (p, r::rs)
  fun merge (p1, r1) (p2, r2) =
    (case S.pcompare (p1, p2) of
      ~1 => (p2, r2)
    | 0 => (p1, r1 @ r2)
    | 1 => (p1, r1)
    | _ => raise Fail "Compiler error")
  fun stringOfInfo (InfoToken e) = S.stringOfElem e
    | stringOfInfo (InfoMessage e) = e
  fun stringOfErrors ([]) = "\n"
    | stringOfErrors (r::rs) = (case r of
        Message s => String.concat ["Message: ", s]
      | Expected e => String.concat ["Expected: ", stringOfInfo e]
      | Unexpected e => String.concat ["Unxpected: ", stringOfInfo e]
      ) ^ "\n" ^ (stringOfErrors rs)
end
