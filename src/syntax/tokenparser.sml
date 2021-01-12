structure MTSTokenParser : sig
  include PARSER
  val getTokenStream : string -> TokenStream.stream monad
  val putSyntaxTree : string -> Syntax.program -> unit monad
  val printMsg : string -> unit monad
  val intLit : int monad
  val boolLit : bool monad
  val lpar : elem monad
  val rpar : elem monad
  val period : elem monad
  val colon : elem monad
  val semicolon : elem monad
  val pipe : elem monad
  val defined : elem monad
  val rightarrow : elem monad
  val underscore : elem monad
  val ident : string monad
  val kwFuncT : elem monad
  val kwSig : elem monad
  val kwFunctor : elem monad
  val kwStruct : elem monad
  val kwTransparent : elem monad
  val kwSet : elem monad
  val kwType : elem monad
  val kwComp : elem monad
  val kwTrans : elem monad
  val kwForAll : elem monad
  val kwFun : elem monad
  val kwCase : elem monad
  val kwOf : elem monad
  val kwIf : elem monad
  val kwThen : elem monad
  val kwElse : elem monad
  val kwLet : elem monad
  val kwIn : elem monad
  val kwEnd : elem monad
  val kwInt : elem monad
  val kwBool : elem monad
  val kwInductive : elem monad
  val kwFixpoint : elem monad
  val kwModule : elem monad
  val kwVal : elem monad
end = struct
  structure Base = MTSCompilerM
  type pos = TokenStream.pos
  type elem = TokenStream.item
  structure TP = ParserT (
    structure S = TokenStream;
    type e = unit;
    structure Base = Base)
  open TP

  fun printMsg s = lift (MTSCompilerM.printMsg s)

  fun expectedKeyword s = throwHere ([Err.Expected (
    Err.InfoMessage (String.concat ["keyword ", s]))])

  val intLit = satisfies (fn (p, x) => case x of
    MTSToken.Integer _ => true | _ => false) >>= (fn (p, x) =>
      (case x of MTSToken.Integer i => return i
        | _ => raise Fail "Compiler bug"))
    ++ throwHere ([Err.Expected (Err.InfoMessage "integer literal")])
  val boolLit = satisfies (fn (p, x) => case x of
    MTSToken.Boolean _ => true | _ => false) >>= (fn (p, x) =>
      (case x of MTSToken.Boolean b => return b
        | _ => raise Fail "Compiler bug"))
    ++ throwHere ([Err.Expected (Err.InfoMessage "boolean literal")])
  val lpar = satisfies (fn (_, x) => x = MTSToken.LPar)
    ++ throwHere ([Err.Message "lpar"])
  val rpar = satisfies (fn (_, x) => x = MTSToken.RPar)
    ++ throwHere ([Err.Message "rpar"])
  fun matchSymbol s =
    (satisfies (fn (_, x) => case x of
    MTSToken.Symbol s' =>
      let val _ = debugPrintline (String.concat ["matchsym ", s, " ", s', "\n"]) in
    s = s' end | _ => false))
    ++ throwHere ([Err.Expected (Err.InfoMessage s)])
  val period = matchSymbol "."
  val colon = matchSymbol ":"
  val semicolon = matchSymbol ";"
  val pipe = matchSymbol "|"
  val defined = matchSymbol ":="
  val rightarrow = matchSymbol "=>"
  val underscore = matchSymbol "_"
  val ident = satisfies (fn (p, x) => case x of
    MTSToken.Identifier _ => true | _ => false) >>= (fn (p, x) =>
      (case x of MTSToken.Identifier s => return s
        | _ => raise Fail "Compiler bug"))
    ++ throwHere ([Err.Expected (Err.InfoMessage "identifier")])
  val kwFuncT = satisfies (fn (p, x) => x = MTSToken.KWFuncT)
    ++ expectedKeyword "funcT"
  val kwSig = satisfies (fn (p, x) => x = MTSToken.KWSig)
    ++ expectedKeyword "sig"
  val kwFunctor = satisfies (fn (p, x) => x = MTSToken.KWFunctor)
    ++ expectedKeyword "functor"
  val kwStruct = satisfies (fn (p, x) => x = MTSToken.KWStruct)
    ++ expectedKeyword "struct"
  val kwTransparent = satisfies (fn (p, x) => x = MTSToken.KWTransparent)
    ++ expectedKeyword "transparent"
  val kwSet = satisfies (fn (p, x) => x = MTSToken.KWSet)
    ++ expectedKeyword "Set"
  val kwType = satisfies (fn (p, x) => x = MTSToken.KWType)
    ++ expectedKeyword "Type"
  val kwComp = satisfies (fn (p, x) => x = MTSToken.KWComp)
    ++ expectedKeyword "Comp"
  val kwTrans = satisfies (fn (p, x) => x = MTSToken.KWTrans)
    ++ expectedKeyword "Trans"
  val kwForAll = satisfies (fn (p, x) => x = MTSToken.KWForAll)
    ++ expectedKeyword "forall"
  val kwFun = satisfies (fn (p, x) => x = MTSToken.KWFun)
    ++ expectedKeyword "fun"
  val kwCase = satisfies (fn (p, x) => x = MTSToken.KWCase)
    ++ expectedKeyword "case"
  val kwOf = satisfies (fn (p, x) => x = MTSToken.KWOf)
    ++ expectedKeyword "of"
  val kwIf = satisfies (fn (p, x) => x = MTSToken.KWIf)
    ++ expectedKeyword "if"
  val kwThen = satisfies (fn (p, x) => x = MTSToken.KWThen)
    ++ expectedKeyword "then"
  val kwElse = satisfies (fn (p, x) => x = MTSToken.KWElse)
    ++ expectedKeyword "else"
  val kwLet = satisfies (fn (p, x) => x = MTSToken.KWLet)
    ++ expectedKeyword "let"
  val kwIn = satisfies (fn (p, x) => x = MTSToken.KWIn)
    ++ expectedKeyword "in"
  val kwEnd = satisfies (fn (p, x) => x = MTSToken.KWEnd)
    ++ expectedKeyword "end"
  val kwInt = satisfies (fn (p, x) => x = MTSToken.KWInt)
    ++ expectedKeyword "int"
  val kwBool = satisfies (fn (p, x) => x = MTSToken.KWBool)
    ++ expectedKeyword "bool"
  val kwInductive = satisfies (fn (p, x) => x = MTSToken.KWInductive)
    ++ expectedKeyword "inductive"
  val kwFixpoint = satisfies (fn (p, x) => x = MTSToken.KWFixpoint)
    ++ expectedKeyword "fixpoint"
  val kwModule = satisfies (fn (p, x) => x = MTSToken.KWModule)
    ++ expectedKeyword "module"
  val kwVal = satisfies (fn (p, x) => x = MTSToken.KWVal)
    ++ expectedKeyword "val"
  fun getTokenStream n = lift (MTSCompilerM.getTokenStream n)
  fun putSyntaxTree n synt = lift (MTSCompilerM.putSyntaxTree n synt)
end

structure MTSTokenParserUtil = MUtil (structure M = MTSTokenParser)

