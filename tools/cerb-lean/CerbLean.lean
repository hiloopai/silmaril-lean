import Silmaril.Cerberus.Cabs.Main.Defs

/-! Entry point of `lake exe cerb-lean` (driver: `Silmaril/Cerberus/Cabs/Main.lean`). -/

def main (args : List String) : IO UInt32 :=
  Silmaril.Cerberus.Cabs.Main.run args
