signature STRM =
sig
  type stream
  type elem
  val uncons : stream -> (elem * stream) option
  val reset : stream * int -> stream
  val pos : stream -> int
end

functor StreamFunctor (S : MONO_VECTOR) : STRM =
struct
  type stream = { s : S.vector, pos : int }
  type elem = S.elem

  fun uncons (strm) = 
  let
    val pos = #pos strm
    val len = S.length (#s strm)
  in
    if pos < len then
      SOME (S.sub (#s strm, pos), { s = #s strm, pos = pos + 1 })
    else NONE
  end

  fun reset (strm, r) =
    { s = #s strm, pos = r }

  fun pos (strm) = #pos strm

end

functor ParserFunctor (S : STRM) :
sig
  include MONADPLUSZERO
  type item
  datatype 'output ParseResult =
    Ok of 'output * S.stream
  | Error of S.stream
  type 'output Parser
  val fail : 'a monad
  val many : 'output Parser -> 'output list Parser
  val many1 : 'output Parser -> 'output list Parser
end
=
struct
  type item = S.elem
  datatype 'output ParseResult =
    Ok of 'output * S.stream
  | Error of S.stream
  type 'output Parser = S.stream -> 'output ParseResult
  type 'a monad = 'a Parser

  fun return x = (fn strm => Ok (x, strm))

  val fail = (fn strm => Error (strm))

  fun op >>= (p, f) = 
    (fn (strm : S.stream) =>
    let val pos = S.pos strm
    in
      (case p strm of
        Ok (x, strm') => f x strm'
      | Error (strm') => Error strm')
    end)

  val zero = (fn (strm : S.stream) => Error strm)

  fun op ++ (p1 : 'a Parser, p2 : 'a Parser) : 'a Parser =
    (fn (strm : S.stream) => 
    let val pos = S.pos strm
    in
      (case p1 strm of
        Error e1 =>
          (case p2 strm of
            Error e2 => Error e1
          | Ok r => Ok r)
      | Ok r => Ok r
      )
    end)

  fun many (p : 'a Parser) : 'a list Parser =
    p >>= (fn x =>
    many p >>= (fn y =>
      return (x::y)
    ))
    ++ (return [])

  fun many1 (p : 'a Parser) : 'a list Parser =
    p >>= (fn x =>
    many p >>= (fn y =>
      return (x::y)
    ))
end


