import Silmaril.Wasm.Binaryen.Toolkit.CompatMetaDCEMain

def main (args : List String) : IO UInt32 :=
  Silmaril.Wasm.Binaryen.Toolkit.runCompatMetaDCE args
