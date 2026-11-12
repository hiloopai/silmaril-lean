module

public import Silmaril.Proofs.Wasm.SpecTec.Surface.Parser

/-!
# SpecTec surface parser: theorems

`parse?_sound`: every declaration list `parse?` returns is a `Parses`
derivation of the tokens, by the productions of `parser.mly` for the fragment
and the span rule for everything else.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Surface.Parser

open Silmaril.Wasm.SpecTec.Surface.Lexer (Token)
open Silmaril.Wasm.SpecTec.Surface.Syntax

/-- The parser is sound: its output is a derivation of the tokens (`Parses`). -/
theorem parse?_sound {ts : List Token} {ds : List Def} (h : parse? ts = some ds) : Parses ts ds :=
  parseList_sound _ _ h

end Silmaril.Wasm.SpecTec.Surface.Parser
