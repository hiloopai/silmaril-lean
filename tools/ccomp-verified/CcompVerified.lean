import Silmaril.Compiler.Core.Main.Defs
/-! Entry point of `lake exe ccomp-verified` (driver `Silmaril/Compile/Core/Main.lean`). -/

def main (args : List String) : IO UInt32 :=
  Silmaril.Compile.Core.Main.main args
