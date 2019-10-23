structure Tokenizer : 
sig
  datatype token =
    Identifier of string
  | Integer of int
  | KWInt
  | KWBool
  | True
  | False
  | First
  | Second
  | ForAll
  | Pi
  | Sigma
  | Val
  | Let
  | In
  | End
  | Fun
  | Fn
  | If
  | Then
  | Else
  | LPar
  | RPar
  | Plus
  | Dash
  | Star
  | Slash
  | Equal
  | EqualEqual
  | NotEqual
  | Less
  | Greater
  | LessEq
  | GreaterEq
  | RightArrow
  | RightDashArrow
  | Colon
  | Comma
  | EOI

  structure TokenVector : MONO_VECTOR
  structure TokenStream : STRM

  val whitespace : unit -> char list CParser.Parser
  val word : unit -> token CParser.Parser
  val integer : unit -> token CParser.Parser
  val lpar : unit -> token CParser.Parser
  val rpar : unit -> token CParser.Parser
  val sym : unit -> token CParser.Parser
  val tok : unit -> token CParser.Parser
  val tokenize : CharStream.stream -> TokenStream.stream
end
=
struct
  datatype token =
    Identifier of string
  | Integer of int
  | KWInt
  | KWBool
  | True
  | False
  | First
  | Second
  | ForAll
  | Pi
  | Sigma
  | Val
  | Let
  | In
  | End
  | Fun
  | Fn
  | If
  | Then
  | Else
  | LPar
  | RPar
  | Plus
  | Dash
  | Star
  | Slash
  | Equal
  | EqualEqual
  | NotEqual
  | Less
  | Greater
  | LessEq
  | GreaterEq
  | RightArrow
  | RightDashArrow
  | Colon
  | Comma
  | EOI

  open CParser

  structure TokenVector : MONO_VECTOR =
  struct
    open Vector
    type vector = token vector
    and elem = token
  end

  structure TokenStream = StreamFunctor (TokenVector)

  fun whitespace () : char list Parser =
    many (CharParser.space ())

  fun word () : token Parser =
    CharParser.letter () >>= (fn (x : char) =>
    many (CharParser.alphanum ()) >>= (fn y =>
      case (String.implode (x::y)) of
        "forall" => return ForAll
      | "pi" => return Pi
      | "sigma" => return Sigma
      | "val" => return Val
      | "let" => return Let
      | "in" => return In
      | "end" => return End
      | "fun" => return Fun
      | "fn" => return Fn
      | "if" => return If
      | "then" => return Then
      | "else" => return Else
      | "int" => return KWInt
      | "bool" => return KWBool
      | "true" => return True
      | "false" => return False
      | "fst" => return First
      | "snd" => return Second
      | _ => return (Identifier (String.implode (x::y)))
    ))

  fun integer () : token Parser =
    many1 (CharParser.digit ()) >>= (fn x =>
      return (Integer (Option.valOf (Int.fromString (String.implode x))))
    )

  fun lpar () : token Parser =
    CharParser.lpar () >>= (fn x =>
      return LPar
    )

  fun rpar () : token Parser =
    CharParser.rpar () >>= (fn x =>
      return RPar
    )

  fun comma () : token Parser =
    CharParser.comma () >>= (fn x =>
      return Comma
    )

  fun sym () : token Parser =
    many1 (CharParser.symbol ()) >>= (fn x =>
      (case String.implode x of
        "+" => return Plus
      | "-" => return Dash
      | "*" => return Star
      | "/" => return Slash
      | "=" => return Equal
      | "==" => return EqualEqual
      | "<>" => return NotEqual
      | "<" => return Less
      | ">" => return Greater
      | "<=" => return LessEq
      | ">=" => return GreaterEq
      | "=>" => return RightArrow
      | "->" => return RightDashArrow
      | ":" => return Colon
      | _ => raise Fail ("not symbol: " ^ (String.implode x))
    ))

  fun tok () : token Parser =
    (word ()
    ++ integer ()
    ++ lpar ()
    ++ rpar ()
    ++ sym ())
    >>= (fn x =>
    whitespace () >>= (fn _ =>
      return x
    ))

  fun tokenize (s : CharStream.stream) : TokenStream.stream =
    case many (tok ()) s of
      Ok (x, xs) => { pos = 0, s = TokenVector.fromList (x @ [EOI]) }
    | Error _ => { pos = 0, s = TokenVector.fromList [] }

end

