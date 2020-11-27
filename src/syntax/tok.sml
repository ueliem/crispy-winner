structure TErr = struct
  type err = unit
  type pos = CharFileStream.pos
  type elem = CharFileStream.elem
end

structure Tokenizer : sig
  include PARSER
  datatype t =
    Identifier of string
  | Integer of int | Boolean of bool
  | LPar | RPar
  (* | Period | Colon | Semicolon | Pipe
  | Defined *)
  | Symbol of string
  | KWFuncT | KWSig
  | KWFunctor | KWStruct | KWTransparent
  | KWSet | KWType | KWComp | KWTrans
  | KWForAll | KWFun | KWCase | KWOf
  | KWIf | KWThen | KWElse
  | KWLet | KWIn | KWEnd
  | KWInt | KWBool
  type tok = CharFileStream.pos * t
  val whitespace : char list monad
  val keyword : t monad
  val ident : t monad
  val integer : t monad
  val lpar : t monad
  val rpar : t monad
  val token : tok monad
  val tokenize : tok list monad
end = struct
  structure CFP = CharFileParser (structure E = TErr)
  open CFP
  datatype t =
    Identifier of string
  | Integer of int | Boolean of bool
  | LPar | RPar
  (* | Period | Colon | Semicolon | Pipe
  | Defined *)
  | Symbol of string
  | KWFuncT | KWSig
  | KWFunctor | KWStruct | KWTransparent
  | KWSet | KWType | KWComp | KWTrans
  | KWForAll | KWFun | KWCase | KWOf
  | KWIf | KWThen | KWElse
  | KWLet | KWIn | KWEnd
  | KWInt | KWBool
  type tok = CharFileStream.pos * t
  val whitespace = many space
  val keyword =
    many1 letter >>= (fn x =>
    case String.implode x of
      "funcT" => return KWFuncT
    | "sig" => return KWSig
    | "functor" => return KWFunctor
    | "struct" => return KWStruct
    | "transparent" => return KWTransparent
    | "Set" => return KWSet
    | "Type" => return KWType
    | "Comp" => return KWComp
    | "Trans" => return KWTrans
    | "forall" => return KWForAll
    | "fun" => return KWFun
    | "case" => return KWCase
    | "of" => return KWOf
    | "if" => return KWIf
    | "then" => return KWThen
    | "else" => return KWElse
    | "let" => return KWLet
    | "in" => return KWIn
    | "end" => return KWEnd
    | "int" => return KWInt
    | "bool" => return KWBool
    | "true" => return (Boolean true)
    | "false" => return (Boolean false)
    | _ => zero ())
  val ident =
    letter >>= (fn x =>
    many alphanum >>= (fn xs =>
    return (Identifier (String.implode (x::xs)))))
  val integer =
    many1 digit >>= (fn x =>
      return (Integer (Option.valOf (Int.fromString (String.implode x)))))
  val sym =
    many1 (symbol) >>= (fn x => return (Symbol (String.implode x)))
  val lpar = lpar >>= (fn x => return LPar)
  val rpar = rpar >>= (fn x => return RPar)
  val token =
    position >>= (fn p =>
    (keyword
    ++ ident
    ++ sym
    ++ integer
    ++ lpar ++ rpar)
    >>= (fn x =>
    whitespace >>= (fn _ =>
      let val _ = PolyML.print p
      in return (p, x) end)))
  val tokenize = many1 token >>= (fn ts => eoi >>= (fn _ => return ts))

end

