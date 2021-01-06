fun main () =
  let
    val _ = TextIO.output (TextIO.stdOut, "start\n")
    val _ = Compiler.compile "examples/nat.crp"
      ([], [], [])
      { files = [], toplevelEnv = [] }
      0
  in
    TextIO.output (TextIO.stdOut, "done\n")
  end

val _ = main ()

