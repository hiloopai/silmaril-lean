module

public import Silmaril.Proofs.Wasm.SpecTec.AstText.Check
public import Silmaril.Proofs.Wasm.SpecTec.AstText.Compose
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The three pinned streams, read by the verified reader

`spectec_check_stream` (`Check.lean`) runs here, in compiled code, on the three vendored files.
**The link to the files is this compiled check, not the kernel.**

What the kernel does check is the other half: `wasmNNText`, *defined* as the printer's output
`astFile 80 (scriptS Specs.wasmNN)`, reads back as `Specs.wasmNN` under the verified reader
(`importAstText?_wasm30Text`). The side condition of the round trip is discharged by computing
`realsScript Specs.wasmNN = []` in the kernel (the pinned scripts contain no `real` numerals),
about 30 s for wasm-3.0. Together with the compiled check that `wasmNNText` *is* the file's
contents, this says the verified reader turns the vendored file into `Specs.wasmNN`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.AstText

open Silmaril.SpecTec

spectec_check_stream Specs.wasm10 against "specs/spectec/wasm-1.0.ast"
spectec_check_stream Specs.wasm20 against "specs/spectec/wasm-2.0.ast"
spectec_check_stream Specs.wasm30 against "specs/spectec/wasm-3.0.ast"

open Silmaril.SpecTec.SExp (astFile defaultWidth)

set_option maxRecDepth 100000

/-- The printer's output for the pinned wasm-1.0 script; `spectec_check_stream` above checks
that it is the contents of `specs/spectec/wasm-1.0.ast`. -/
noncomputable def wasm10Text : String := astFile defaultWidth (IL.scriptS Specs.wasm10)

/-- The pinned wasm-1.0 script has no `real` numerals. -/
theorem realsScript_wasm10 : IL.realsScript Specs.wasm10 = [] := by rfl

theorem astTextRel_wasm10Text : AstTextRel wasm10Text Specs.wasm10 :=
  astTextRel_astFile _ _ (realsScript_wasm10 ▸ fun _ h => nomatch h)

theorem importAstText?_wasm10Text : importAstText? wasm10Text = some Specs.wasm10 :=
  importAstText?_complete _ _ astTextRel_wasm10Text

/-- The printer's output for the pinned wasm-2.0 script; `spectec_check_stream` above checks
that it is the contents of `specs/spectec/wasm-2.0.ast`. -/
noncomputable def wasm20Text : String := astFile defaultWidth (IL.scriptS Specs.wasm20)

/-- The pinned wasm-2.0 script has no `real` numerals. -/
theorem realsScript_wasm20 : IL.realsScript Specs.wasm20 = [] := by rfl

theorem astTextRel_wasm20Text : AstTextRel wasm20Text Specs.wasm20 :=
  astTextRel_astFile _ _ (realsScript_wasm20 ▸ fun _ h => nomatch h)

theorem importAstText?_wasm20Text : importAstText? wasm20Text = some Specs.wasm20 :=
  importAstText?_complete _ _ astTextRel_wasm20Text

/-- The printer's output for the pinned wasm-3.0 script; `spectec_check_stream` above checks
that it is the contents of `specs/spectec/wasm-3.0.ast`. -/
noncomputable def wasm30Text : String := astFile defaultWidth (IL.scriptS Specs.wasm30)

/-- The pinned wasm-3.0 script has no `real` numerals. -/
theorem realsScript_wasm30 : IL.realsScript Specs.wasm30 = [] := by rfl

theorem astTextRel_wasm30Text : AstTextRel wasm30Text Specs.wasm30 :=
  astTextRel_astFile _ _ (realsScript_wasm30 ▸ fun _ h => nomatch h)

theorem importAstText?_wasm30Text : importAstText? wasm30Text = some Specs.wasm30 :=
  importAstText?_complete _ _ astTextRel_wasm30Text

end Silmaril.Wasm.SpecTec.AstText
