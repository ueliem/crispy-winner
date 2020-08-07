structure Tokenizer : 
sig
  datatype tok =
    Identifier of string
  | Integer of int
  | KWInt
  | KWBool
  | KWUnit
  | KWUnbox
  | KWElim
  | KWType
  | True
  | False
  | Select
  | ForAll
  | Pi
  | Sigma
  | Val
  | Let
  | LetRegion
  | At
  | In
  | End
  | Fun
  | Fn
  | If
  | Then
  | Else
  | UnitSymbol
  | LPar
  | RPar
  | LCurly
  | RCurly
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

  type token = CharFileStream.pos * tok

  structure TokenVector : MONO_VECTOR
  structure TokenStream : sig
    include STRM
  end

  val whitespace : unit -> char list FileCharParser.Parser
  val word : unit -> tok FileCharParser.Parser
  val integer : unit -> tok FileCharParser.Parser
  val unitsymbol : unit -> tok FileCharParser.Parser
  val lpar : unit -> tok FileCharParser.Parser
  val rpar : unit -> tok FileCharParser.Parser
  val sym : unit -> tok FileCharParser.Parser
  val tok : unit -> token FileCharParser.Parser
  val tokenize : CharFileStream.stream -> TokenStream.stream
end
=
struct
  datatype tok =
    Identifier of string
  | Integer of int
  | KWInt
  | KWBool
  | KWUnit
  | KWUnbox
  | KWElim
  | KWType
  | True
  | False
  | Select
  | ForAll
  | Pi
  | Sigma
  | Val
  | Let
  | LetRegion
  | At
  | In
  | End
  | Fun
  | Fn
  | If
  | Then
  | Else
  | UnitSymbol
  | LPar
  | RPar
  | LCurly
  | RCurly
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

  type token = CharFileStream.pos * tok

  structure TokenVector : MONO_VECTOR =
  struct
    open Vector
    type vector = token vector
    and elem = token
  end

  structure TokenStream = 
  struct
    structure TS = StreamFunctor (structure S = TokenVector;
      val eq = (fn (x, y) => x = y);
      val estr = (fn (p, t) => 
        (case t of
          Identifier i => String.concat ["identifier", i]
        | Integer i => String.concat ["integer ", Int.toString i]
        | KWInt => "int"
        | KWBool => "bool"
        | KWUnit => "unit"
        | KWUnbox => "unbox"
        | KWElim => "elim"
        | KWType => "type"
        | True => "true"
        | False => "false"
        | Select => "sel"
        | ForAll => "forall"
        | Pi => "pi"
        | Sigma => "sigma"
        | Val => "val"
        | Let => "let"
        | LetRegion => "letregion"
        | At => "at"
        | In => "in"
        | End => "end"
        | Fun => "fun"
        | Fn => "fn"
        | If => "if"
        | Then => "then"
        | Else => "else"
        | UnitSymbol => "()"
        | LPar => "("
        | RPar => ")"
        | LCurly => "{"
        | RCurly => "}"
        | Plus => "+"
        | Dash => "-"
        | Star => "*"
        | Slash => "/"
        | Equal => "="
        | EqualEqual => "=="
        | NotEqual => "!="
        | Less => "<"
        | Greater => ">"
        | LessEq => "<="
        | GreaterEq => ">="
        | RightArrow => "->"
        | RightDashArrow => "=>"
        | Colon => ":"
        | Comma => ","
        | EOI => "EOI"
        )))

    type pos = int * int
    type stream = { s : TS.stream }
    type elem = TS.elem

    fun uncons (strm) = 
      (case TS.uncons (#s strm) of
        SOME (t, s') => SOME (t, { s = s' })
      | NONE => NONE)

    fun position (strm) =
      (case TS.peek (#s strm) of
        SOME (p, t) => p
      | NONE => (~1, ~1)) (* raise Fail "pos") *)

    val equiv = TS.equiv

    fun pcompare ((l1, c1), (l2, c2)) =
      if l1 < l2 then ~1
      else if l1 = l2 then
        if c1 < c2 then ~1
        else if c1 = c2 then 0
        else 1
      else 1

    fun pos_to_string (l, c) =
      String.concat ["line ", Int.toString l, " column ", Int.toString c]

    fun elem_to_string (p, t) = 
      String.concat [TS.elem_to_string (p, t), "(", pos_to_string p, ")"]

    fun peek (strm) = TS.peek (#s strm)
  end

  open FileCharParser

  fun whitespace () : char list Parser =
    many (FileCharParser.space ())

  fun word () : tok Parser =
    FileCharParser.letter () >>= (fn (x : char) =>
    many (FileCharParser.alphanum ()) >>= (fn y =>
      case (String.implode (x::y)) of
        "forall" => return ForAll
      | "pi" => return Pi
      | "sigma" => return Sigma
      | "val" => return Val
      | "let" => return Let
      | "letregion" => return LetRegion
      | "at" => return At
      | "in" => return In
      | "end" => return End
      | "fun" => return Fun
      | "fn" => return Fn
      | "if" => return If
      | "then" => return Then
      | "else" => return Else
      | "int" => return KWInt
      | "bool" => return KWBool
      | "unit" => return KWUnit
      | "true" => return True
      | "false" => return False
      | "unbox" => return KWUnbox
      | "elim" => return KWElim
      | "sel" => return Select
      | "type" => return KWType
      | _ => return (Identifier (String.implode (x::y)))
    ))

  fun integer () : tok Parser =
    many1 (FileCharParser.digit ()) >>= (fn x =>
      return (Integer (Option.valOf (Int.fromString (String.implode x))))
    )

  fun unitsymbol () : tok Parser =
    FileCharParser.lpar () >>= (fn x =>
    FileCharParser.rpar () >>= (fn y =>
      return UnitSymbol
    ))

  fun lpar () : tok Parser =
    FileCharParser.lpar () >>= (fn x =>
      return LPar
    )

  fun rpar () : tok Parser =
    FileCharParser.rpar () >>= (fn x =>
      return RPar
    )

  fun lcurly () : tok Parser =
    FileCharParser.lcurly () >>= (fn x =>
      return LCurly
    )

  fun rcurly () : tok Parser =
    FileCharParser.rcurly () >>= (fn x =>
      return RCurly
    )

  fun comma () : tok Parser =
    FileCharParser.comma () >>= (fn x =>
      return Comma
    )

  fun sym () : tok Parser =
    many1 (FileCharParser.symbol ()) >>= (fn x =>
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
    position () >>= (fn p =>
    (word ()
    ++ integer ()
    ++ unitsymbol ()
    ++ lpar ()
    ++ rpar ()
    ++ lcurly ()
    ++ rcurly ()
    ++ sym ())
    >>= (fn x =>
    whitespace () >>= (fn _ =>
      let val _ = PolyML.print p
      in
        return (p, x)
      end
    )))

  fun tokenize (s : CharFileStream.stream) : TokenStream.stream =
    case many (tok ()) s of
      (Ok (x), s') =>
        let val p = CharFileStream.position s'
        in
          { s = { pos = 0, s = TokenVector.fromList (x @ [(p, EOI)]) } }
        end
    | (Error _, s') => { s = { pos = 0, s = TokenVector.fromList [] } }

end

