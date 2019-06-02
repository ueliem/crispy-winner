signature STREAM =
sig
  type 'a stream
  val uncons : 'a stream -> ('a * 'a stream) option
  val reset : 'a stream * int -> 'a stream
  val pos : 'a stream -> int
end

structure Stream : STREAM =
struct
  type 'a stream = { s : 'a vector, pos : int }

  fun uncons (strm) = 
  let
    val pos = #pos strm
    val len = Vector.length (#s strm)
  in
    if pos < len then
      SOME (Vector.sub (#s strm, pos), { s = #s strm, pos = pos + 1 })
    else NONE
  end

  fun reset (strm, r) =
    { s = #s strm, pos = r }

  fun pos (strm) = #pos strm

end

signature PARSER =
sig
  include MONADPLUSZERO
  type item
  datatype 'output ParseResult =
    Ok of 'output * item Stream.stream
  | Error of item Stream.stream
  type 'output Parser
  val fail : 'a monad
  val many : 'output Parser -> 'output list Parser
  val many1 : 'output Parser -> 'output list Parser
end

functor ParserFunctor (type item) : PARSER =
struct
  type item = item
  datatype 'output ParseResult =
    Ok of 'output * item Stream.stream
  | Error of item Stream.stream
  type 'output Parser = item Stream.stream -> 'output ParseResult
  type 'a monad = 'a Parser

  fun return x = (fn strm => Ok (x, strm))

  val fail = (fn strm => Error (strm))

  fun op >>= (p, f) = 
    (fn (strm : item Stream.stream) =>
    let val pos = Stream.pos strm
    in
      (case p strm of
        Ok (x, strm') => f x strm'
      | Error (strm') => Error strm')
    end)

  val zero = (fn (strm : item Stream.stream) => Error strm)

  fun op ++ (p1 : 'a Parser, p2 : 'a Parser) : 'a Parser =
    (fn (strm : item Stream.stream) => 
    let val pos = Stream.pos strm
    in
      (case p1 strm of
        Error e1 =>
          (case p2 strm of
            Error e2 => Error e1
          | Ok r => Ok r)
      | Ok r => Ok r
      )
      (* (case (p1 strm, p2 strm) of
        (Error _, Error _) => Error strm
      | (Error _, Ok r) => Ok r
      | (Ok r, _) => Ok r
      ) *)
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


