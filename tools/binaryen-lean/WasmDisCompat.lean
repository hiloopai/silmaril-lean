import Silmaril.Wasm.Binaryen.Toolkit.CompatDisMain

def main (args : List String) : IO UInt32 :=
  Silmaril.Wasm.Binaryen.Toolkit.runCompatDis args
