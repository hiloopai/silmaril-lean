import Silmaril.Cerberus.Ail.Main.Defs

/-! Entry point of `lake exe ail-lean` (driver: `Silmaril/Cerberus/Ail/Main.lean`). -/

def main (args : List String) : IO UInt32 :=
  Silmaril.Cerberus.Ail.Main.run args
