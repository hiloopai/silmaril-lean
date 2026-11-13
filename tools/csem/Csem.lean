import Silmaril.Compiler.C.Sem.Main.Defs
/-! Entry point of `lake exe csem` (driver: `Silmaril/Compile/C/Sem/Main.lean`). -/

def main (args : List String) : IO UInt32 :=
  Silmaril.Compile.C.Sem.Main.main args
