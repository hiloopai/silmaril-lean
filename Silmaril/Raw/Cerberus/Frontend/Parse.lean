module

public import Silmaril.Cerberus.Frontend.Grammar.Defs
public import Silmaril.Cerberus.Frontend.Lexer.Defs

/-! # The Cerberus C frontend: parsing

`parse` is what `cerb-lean parse` runs: Cerberus's `C_parser_driver.parse_from_string`
on preprocessed C. Its input is the text the Cerberus parser sees, that is, the `.i`
file without its final newline (`Pipeline.cpp` joins the lines of the cpp output with
`"\n"`). It returns the Cabs translation unit, or the error that Cerberus reports, with
the stage `parse`. `docs/projects/cerberus.md` collects the facts about Cerberus's lexer
and grammar that a byte-exact port needs.

The pipeline: `Lexer.tokens` lexes the whole text, then the recursive descent of
`Declarations.translationUnit` parses it with the typedef names of `TypedefEnv.builtin`
in scope. Constructs the grammar files do not support yet are rejected.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend

open Silmaril.Cerberus

/-- Parse preprocessed C into Cabs, or reject it at the stage `parse`. -/
def parse (input : ByteArray) : Except Cabs.Codec.Reject Cabs.TranslationUnit := do
  let toks ← Lexer.tokens input
  let start : PState := ⟨toks, 0, TypedefEnv.builtin, ⟨"", 1, 1⟩⟩
  let (unit, _) ← (Declarations.translationUnit (Grammar.knot Grammar.depth)).run start
  return unit

end Silmaril.Cerberus.Frontend
