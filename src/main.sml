fun main () =
  let
    fun exit _ = OS.Process.exit (OS.Process.success)
    val _ = Compiler.compile ""
  in
    ()
  end

