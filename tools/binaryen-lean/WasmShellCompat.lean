import Silmaril.Wasm.Binaryen.Toolkit.CompatShellMain

def main (args : List String) : IO UInt32 :=
  Silmaril.Wasm.Binaryen.Toolkit.runCompatShell args
