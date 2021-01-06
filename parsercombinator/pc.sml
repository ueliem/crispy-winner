signature PARSER = sig
  structure S : STREAM
  type s = S.stream
  type pos = S.pos
  type elem = S.item
  type e
  structure Err : PARSERERR
  structure Base : MONAD
  structure PST : STATET
  structure PEXC : EXCEPTIONT
  include MONADPLUS
  val lift : 'a Base.monad -> 'a monad
  val getstate : s monad
  val putstate : s -> unit monad
  val throw : Err.err -> 'a monad
  val throwHere : Err.singleErr list -> 'a monad
  val catch : ('a monad * (Err.err -> 'a monad)) -> 'a monad
  val position : S.pos monad
  val next : S.item monad
  val peek : S.item monad
  val satisfies : (S.item -> bool) -> S.item monad
  val many : 'a monad -> 'a list monad
  val many1 : 'a monad -> 'a list monad
  val optional : 'a monad -> 'a option monad
  val endOfInput : unit monad
end

functor ParserT (structure S : STREAM;
  type e;
  structure Base : MONAD) : sig
    include PARSER end = struct
  structure S = S
  structure Base = Base
  type s = S.stream
  type pos = S.pos
  type elem = S.item
  type e = e
  structure Err = ParserErrT (type e = e; structure S = S)
  structure PST = StateT (type s = s; structure M = Base)
  structure PEXC = ExceptionT (type e = Err.err; structure M = PST)
  (* open PEXC *)
  type 'a monad = 'a PEXC.monad
  val return = PEXC.return
  val op >>= = PEXC.>>=
  val getstate = PEXC.lift PST.get
  val putstate = (fn st => PEXC.lift (PST.put st))
  fun op ++ (m1, m2) =
    getstate >>= (fn st =>
    PST.>>= (m1, (fn x => case x of
      PEXC.ExcVal y => PST.return (PEXC.ExcVal y)
    | PEXC.ExcErr r =>
        PST.>>= (m2, (fn z => case z of
            PEXC.ExcVal y => PST.return (PEXC.ExcVal y)
          | PEXC.ExcErr r' =>
            PST.return (PEXC.ExcErr (Err.merge r r')))))))

  val lift = (fn m => PEXC.lift (PST.lift m))
  val throw = PEXC.throw
  val catch = PEXC.catch
  val position = getstate >>= (fn st => PEXC.return (S.position st))
  fun throwHere rs = position >>= (fn p => let val _ = 
    debugPrintline (String.concat ["throwHere ", S.stringOfPos p, "\n"])
    val _ = debugPrintline (Err.stringOfErrors rs)
    in throw (Err.error p rs) end)
  val next =
    getstate >>= (fn st =>
      (case S.uncons st of
        SOME (x, xs) => putstate xs >>= let val _ =
        debugPrintline (String.concat ["next ", S.stringOfElem x, "\n"])
        in (fn _ => return x) end
      | NONE => throwHere ([Err.unexpectedEOI])))
  val peek = getstate >>= (fn st =>
    (case S.peek st of
      SOME t => let val _ =
        debugPrintline (String.concat ["peek ", S.stringOfElem t, "\n"])
        in return t end
    | NONE => throwHere ([Err.unexpectedEOI])))
  fun satisfies f = 
    peek >>= (fn x =>
    if f x then next else 
    let val _ = 
      debugPrintline (String.concat ["unsat ", S.stringOfElem x, "\n"])
      in throwHere ([Err.Unexpected (Err.InfoToken x)])end)
  fun many p =
    (p >>= (fn x => many p >>= (fn y => return (x::y))))
    ++ (return [])
  fun many1 p =
    (p >>= (fn x => many p >>= (fn y => return (x::y))))
    ++ throwHere ([Err.Message "many1 needs more than zero"])
  fun optional p =
    (p >>= (fn x => return (SOME x)))
    ++ (return NONE)
  val endOfInput =
    getstate >>= (fn st =>
    if S.isEmpty st then return ()
    else throwHere ([Err.expectedEOI]))
end

