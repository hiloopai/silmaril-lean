module

public import Silmaril.Parse.ByteParse.Defs
public import Silmaril.Parse.DecodeGraph.Defs

/-! # Success graphs of the existing ByteParse cursor parser -/

@[expose] public section

namespace Silmaril.Parse.DecodeGraph

variable {Context Buffer : Type*}

/-- Forget diagnostics, preserving exactly the successes of a cursor parser. -/
def successes {Value : Type} (run : Context → Buffer → Nat → Nat → ByteParse.Res Value) :
    Graph Context Buffer Value :=
  {(input, result) | run input.context input.bytes input.stop input.pos = .ok result.1 result.2}

/-- Interpret a canonical context-free parser at `Unit`. -/
def ofParser {Value : Type} (parser : ByteParse.Parser Value) : Graph Unit ByteArray Value :=
  successes fun _ => parser

end Silmaril.Parse.DecodeGraph
