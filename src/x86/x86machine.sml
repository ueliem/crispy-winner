structure X86Machine : sig
  datatype operandsize =
    One
  | Two
  | Four
  | Eight
  type register = string
  type immed = string
  type addr = {
    segment : register option,
    offset : immed,
    base : register option,
    index : register option,
    scale : operandsize
  }
  type prefix =
  {
    instrprefix : Word8.word option,
    addrsizeprefix : Word8.word option,
    operandsizeprefix : Word8.word option,
    segmentoverrideprefix : Word8.word option
  }
  datatype opcode =
    OneByteOp of Word8.word
  | TwoByteOp of Word8.word
  type instr =
  {
    prefix : prefix,
    opcode : opcode,
    modregrm : Word8.word option,
    scaledindexbyte : Word8.word option,
    displacement : Word8.word list,
    immediate : Word8.word list
  }

  val prefixlength : prefix -> int
  val opcodelength : opcode -> int
  val instrlength : instr -> int
  val isvalidinstr : instr -> bool

  val prefixtobytes : prefix -> Word8.word list
  val opcodetobytes : opcode -> Word8.word list
  val instrtobytes : instr -> Word8.word list

end
=
struct
  datatype operandsize =
    One
  | Two
  | Four
  | Eight
  type register = string
  type immed = string
  type addr = {
    segment : register option,
    offset : immed,
    base : register option,
    index : register option,
    scale : operandsize
  }
  type prefix =
  {
    instrprefix : Word8.word option,
    addrsizeprefix : Word8.word option,
    operandsizeprefix : Word8.word option,
    segmentoverrideprefix : Word8.word option
  }
  datatype opcode =
    OneByteOp of Word8.word
  | TwoByteOp of Word8.word
  type instr =
  {
    prefix : prefix,
    opcode : opcode,
    modregrm : Word8.word option,
    scaledindexbyte : Word8.word option,
    displacement : Word8.word list,
    immediate : Word8.word list
  }

  fun prefixlength ({ instrprefix, addrsizeprefix, operandsizeprefix, segmentoverrideprefix }) =
    let
      val i = if isSome instrprefix then 1 else 0
      val a = if isSome instrprefix then 1 else 0
      val z = if isSome instrprefix then 1 else 0
      val s = if isSome instrprefix then 1 else 0
    in
      i + a + z + s
    end

  fun opcodelength (OneByteOp _) = 1
  | opcodelength (TwoByteOp _) = 2

  fun instrlength ({ prefix, opcode, modregrm, scaledindexbyte, displacement, immediate }) = 
    let
      val m = if Option.isSome modregrm then 1 else 0
      val s = if Option.isSome scaledindexbyte then 1 else 0
      val d = List.length displacement
      val i = List.length displacement
    in
      prefixlength prefix + opcodelength opcode + m + s + d + i
    end

  fun isvalidinstr inst =
    instrlength inst <= 15

  fun prefixtobytes ({ instrprefix, addrsizeprefix, operandsizeprefix, segmentoverrideprefix }) =
    let
      val i = if Option.isSome instrprefix then [Option.valOf instrprefix] else []
      val a = if Option.isSome addrsizeprefix then [Option.valOf addrsizeprefix] else []
      val z = if Option.isSome operandsizeprefix then [Option.valOf operandsizeprefix] else []
      val s = if Option.isSome segmentoverrideprefix then [Option.valOf segmentoverrideprefix] else []
    in
      i @ a @ z @ s
    end

  fun opcodetobytes (OneByteOp b) = [b]
  | opcodetobytes (TwoByteOp b) = [Word8.fromInt 15, b]

  fun instrtobytes ({ prefix, opcode, modregrm, scaledindexbyte, displacement, immediate }) =
    let
      val m = if Option.isSome modregrm then [Option.valOf modregrm] else []
      val s = if Option.isSome scaledindexbyte then [Option.valOf scaledindexbyte] else []
    in
      prefixtobytes prefix @ opcodetobytes opcode @ m @ s @ displacement @ immediate
    end

end

