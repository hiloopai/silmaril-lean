import Silmaril.Wasm.Binaryen.Toolkit.ShellMain

def main (args : List String) : IO UInt32 :=
  Silmaril.Wasm.Binaryen.Toolkit.runStandaloneShell args
