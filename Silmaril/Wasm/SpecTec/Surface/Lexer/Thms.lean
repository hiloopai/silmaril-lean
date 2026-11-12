module

public import Silmaril.Proofs.Wasm.SpecTec.Surface.Lexer

/-!
# SpecTec surface lexer: theorems

`lex?_sound`: every token list `lex?` returns is a `Lexes` derivation of the
input, rule by rule of `lexer.mll`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Surface.Lexer

/-- The lexer is sound: its output is a lexing of the input by the rules of
`lexer.mll` (`Lexes`). -/
theorem lex?_sound {s : String} {ts : List Token} (h : lex? s = some ts) : Lexes s.toList ts :=
  lexList?_sound _ _ _ h

end Silmaril.Wasm.SpecTec.Surface.Lexer
