import Silmaril.Compiler.Clang.Main.Defs

/-! Entry point of `lake exe cfront` (driver: `Silmaril/Clang/Main.lean`). -/

def main (args : List String) : IO UInt32 :=
  Silmaril.Clang.Main.main args
