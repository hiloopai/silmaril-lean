module
public import Silmaril.Project.Defs
public import Silmaril.Formats.SExp.EncodingWatFullLexer

/-!
# Format `sexp.wat`

The WAT lexical layer as an S-expression format: UTF-8 text, lexed with the Wasm
Core 3.0 (SpecTec) profile and bracketed into one document of tagged atoms
(`Silmaril.Formats.SExpEncoding.SExp`: keywords, numbers, strings, `$`-ids).
The parser is silmaril-lean's executable `Wat.sexpWatFullExec? .core3`
(`Silmaril/Formats/SExp/EncodingWatFullLexer.lean`); no parser is changed.

It is the S-expression base layer of the `wat.sexp` format. The `sound` law for the
independent lexical relation `Wat.sexpWat .core3` is in
`Silmaril.Project.Formats.SExpWat.Thms`. No printer (none exists for this AST).
-/

@[expose] public section
namespace Silmaril.Project.Formats

open Silmaril.Formats.SExpEncoding

/-- WAT text (Core 3.0 lexical profile) to its S-expression document. -/
def sexpWat : Format blob SExp where
  parse b := String.fromUTF8? b.data >>= Wat.sexpWatFullExec? .core3

/-- The specification relation of `sexp.wat`: the bytes are UTF-8 for a text that
the WAT lexical grammar `Wat.sexpWat .core3` relates to the document. -/
def SExpWatRel (b : Silmaril.Formats.Bytes) (doc : SExp) : Prop :=
  ∃ s, String.fromUTF8? b.data = some s ∧ Wat.sexpWat .core3 s doc

end Silmaril.Project.Formats

silmaril format sexp.wat := Silmaril.Project.Formats.sexpWat
  (doc := "WAT text lexed (Core 3.0 profile) to one S-expression document of tagged atoms (Wat.sexpWatFullExec?)")
