module
public import Silmaril.Project.Formats.SExpWat.Defs
public import Silmaril.Wasm.Binaryen.Toolkit.WatSource
public import Silmaril.Wasm.Binaryen.Toolkit.WatRender

/-!
# Format `wat.sexp`

WebAssembly text (UTF-8) to the Core 3.0 module AST `Silmaril.Wasm.Module`, the value type
of `wasm.binary.core`, so a `.wat` and a `.wasm` artifact can be `Equivalent`.

* Parser: the S-expression layer `sexp.wat` (`Silmaril.Project.Formats.sexpWat`), then
  silmaril-lean's `Binaryen.Toolkit.Wat.parseSupported?` (`WatSource.lean`): the canonical
  numeric fragment, else the source-directed elaborator for named and abbreviated WAT. This
  is the parser of the checked assembler `assembleText`, with the full WAT lexer in front.
* Printer: `Wat.moduleSyntax?` (canonical S-expression of a module) and
  `renderWatDocument?` (checked rendering).

Laws (`Silmaril.Project.Formats.Wat.Thms`): `sound` for the Core text grammar
`Text.Core.Encodes` (`sexpWat3 ⨾ watSyntax`), from `sexpWat_of_fullExec` and
`parseSupported?_sound`. No `roundtrip` law (no completeness theorem for the printer route).

Gap: only the supported fragment is executable. Full WAT is the elaboration-time `wat3!`
frontend, whose specification is the relation `Text.Core.watSyntax`, not a function.
-/

@[expose] public section
namespace Silmaril.Project.Formats

open Silmaril.Wasm.Binaryen.Toolkit

/-- WAT text to the Core module AST, on top of `sexp.wat`. -/
def wat : Format blob Silmaril.Wasm.Module :=
  { sexpWat.andThen Wat.parseSupported? with
    print := some fun m => do
      let doc ← Wat.moduleSyntax? m
      let text ← renderWatDocument? doc
      pure ⟨text.toUTF8⟩ }

/-- The specification relation of `wat.sexp`: UTF-8 text that the Core 3.0 text grammar relates
to the module. -/
def WatRel (b : Silmaril.Formats.Bytes) (m : Silmaril.Wasm.Module) : Prop :=
  ∃ s, String.fromUTF8? b.data = some s ∧ Silmaril.Wasm.Text.Core.Encodes s m

end Silmaril.Project.Formats

silmaril format wat.sexp := Silmaril.Project.Formats.wat (base := sexp.wat)
  (doc := "WebAssembly text to the Core module AST (sexp.wat, then Binaryen.Toolkit.Wat.parseSupported?)")
silmaril format_default wat := wat.sexp
