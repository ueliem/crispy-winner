structure MTSCompilerM = CompilerMT (structure C = struct
  type var = MTS.var
  val eqv = MTS.eqv
  val varOfInt = (fn i => MTS.GenVar i)
  type enventry = MTS.specification
  type pts = MTS.sorts * MTS.ax * MTS.rules
  type err = unit
end)

