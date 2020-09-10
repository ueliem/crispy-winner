structure X86ASM : sig
  type operandsize = X86Machine.operandsize
  type register = string
  datatype immed =
    Literal of int
  | Label of string
  type addr = X86Machine.addr
  datatype dest =
    DestReg of register
  | DestMem of addr
  datatype source =
    SourceReg of register
  | SourceMem of addr
  | SourceImm of immed
  datatype mnem =
    ADD of operandsize * dest * source
  | SUB of operandsize * dest * source
  | MUL of operandsize * dest * source
  | DIV of operandsize * dest * source
  | PUSH of operandsize * source
  | POP of operandsize * dest
  | CALL of operandsize * dest
  | RET of operandsize
  | MOV of operandsize * dest * source
  | CMP of operandsize * dest * source
  | JMP of operandsize * immed
  | JE of operandsize * immed

  type line = string option * mnem * string option

end
=
struct
  type operandsize = X86Machine.operandsize
  type register = string
  datatype immed =
    Literal of int
  | Label of string
  type addr = X86Machine.addr
  datatype dest =
    DestReg of register
  | DestMem of addr
  datatype source =
    SourceReg of register
  | SourceMem of addr
  | SourceImm of immed
  datatype mnem =
    ADD of operandsize * dest * source
  | SUB of operandsize * dest * source
  | MUL of operandsize * dest * source
  | DIV of operandsize * dest * source
  | PUSH of operandsize * source
  | POP of operandsize * dest
  | CALL of operandsize * dest
  | RET of operandsize
  | MOV of operandsize * dest * source
  | CMP of operandsize * dest * source
  | JMP of operandsize * immed
  | JE of operandsize * immed

  type line = string option * mnem * string option

end

