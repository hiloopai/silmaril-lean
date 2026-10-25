import Silmaril.Wasm.Binaryen.Toolkit.CompatAsMain

def main (args : List String) : IO UInt32 :=
  Silmaril.Wasm.Binaryen.Toolkit.runCompatAs args
