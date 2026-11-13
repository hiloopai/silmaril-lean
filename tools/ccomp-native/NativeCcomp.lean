module

public import Silmaril.Compiler.Native.Driver.Defs
@[expose] public section

def main (args : List String) : IO UInt32 :=
  Silmaril.Compiler.Native.Driver.main args
