structure MTSToken = struct
  val symbolList = [#"+", #"-", #"*", #"/",
                 #"/", #"=", #">", #"<",
                 #":", #";", #".", #"|",
                 #"_", #"!", #"~", #"@"]
  datatype t =
      Identifier of string
    | Integer of int | Boolean of bool
    | LPar | RPar
    | Symbol of string
    | KWFuncT | KWSig
    | KWFunctor | KWStruct | KWTransparent
    | KWSet | KWType | KWComp | KWTrans
    | KWForAll | KWFun | KWCase | KWOf
    | KWIf | KWThen | KWElse
    | KWLet | KWIn | KWEnd
    | KWInt | KWBool | KWInductive
    | KWFixpoint | KWModule | KWVal
  fun makeKeyword s = case s of
      "funcT" => SOME KWFuncT
    | "sig" => SOME KWSig
    | "functor" => SOME KWFunctor
    | "struct" => SOME KWStruct
    | "transparent" => SOME KWTransparent
    | "Set" => SOME KWSet
    | "Type" => SOME KWType
    | "Comp" => SOME KWComp
    | "Trans" => SOME KWTrans
    | "forall" => SOME KWForAll
    | "fun" => SOME KWFun
    | "case" => SOME KWCase
    | "of" => SOME KWOf
    | "if" => SOME KWIf
    | "then" => SOME KWThen
    | "else" => SOME KWElse
    | "let" => SOME KWLet
    | "in" => SOME KWIn
    | "end" => SOME KWEnd
    | "int" => SOME KWInt
    | "bool" => SOME KWBool
    | "true" => SOME (Boolean true)
    | "false" => SOME (Boolean false)
    | "inductive" => SOME (KWInductive)
    | "fixpoint" => SOME (KWFixpoint)
    | "module" => SOME (KWModule)
    | "val" => SOME (KWVal)
    | _ => NONE
  fun makeIdentifier s = Identifier s
  fun makeInteger s = (case Int.fromString s of
    SOME i => SOME (Integer i) | NONE => NONE)
  fun makeSymbol s = Symbol s
  fun makeLPar () = LPar
  fun makeRPar () = RPar
  fun stringOf t = (case t of
      Identifier s => "id:" ^ s
    | Integer i => Int.toString i
    | Boolean true => "true"
    | Boolean false => "false"
    | LPar => "("
    | RPar => ")"
    | Symbol s => s
    | KWFuncT => "funcT"
    | KWSig => "sig"
    | KWFunctor => "functor"
    | KWStruct => "struct"
    | KWTransparent => "transparent"
    | KWSet => "Set"
    | KWType => "Type"
    | KWComp => "Comp"
    | KWTrans => "Trans"
    | KWForAll => "forall"
    | KWFun => "fun"
    | KWCase => "case"
    | KWOf => "of"
    | KWIf => "if"
    | KWThen => "then"
    | KWElse => "else"
    | KWLet => "let"
    | KWIn => "in"
    | KWEnd => "end"
    | KWInt => "int"
    | KWBool => "bool"
    | KWInductive => "inductive"
    | KWFixpoint => "fixpoint"
    | KWModule => "module"
    | KWVal => "val")
end
