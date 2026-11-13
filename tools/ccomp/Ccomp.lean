import Silmaril.Compiler.C.Main.Defs
/-! Entry point of `lake exe ccomp` (driver: `Silmaril/Compile/C/Main.lean`). -/

def main (args : List String) : IO UInt32 :=
  Silmaril.Compile.C.Main.main args
