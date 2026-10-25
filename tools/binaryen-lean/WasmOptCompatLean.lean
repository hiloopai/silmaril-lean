import Silmaril.Wasm.Binaryen.Exe.OptCompatMain

def main (args : List String) : IO UInt32 :=
  Silmaril.Wasm.Binaryen.Exe.runOptCompat args
