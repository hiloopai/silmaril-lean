module

public import Silmaril.Wasm.SpecTec.Meta.Errata.Defs
public import Silmaril.Raw.Wasm.SpecTec.Scripts.MetaIL.Fixed
public import Silmaril.Wasm.SpecTec.AstText.Thms
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Valid
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Valid
import all Silmaril.Wasm.SpecTec.Meta.Errata.Defs

/-!
# The meta-theory IL script through our pipeline

`specs/spectec/meta-theory-3a10283c5b/meta-il.ast` is read four ways, and they agree:

* `tools/spectec-gen` (Rust) writes it as Lean source, `Scripts.MetaIL.Original.script`;
* `spectec_import` (Lean, elaboration time) reads it as `Specs.metail`, and
  `generated_metail_eq` proves the two are the same term;
* the verified reader (`AstText`, `SExp.parseStream?` then `decodeScript?`) reads the file as
  `scriptS Specs.metail`, and the printer reprints it byte for byte (`spectec_check_stream`,
  compiled); `importAstText?_metailText` is the kernel statement for the printed text;
* the typing-free well-formedness checker (`Sem/Valid.lean`, a transcription of `il/valid.ml`)
  accepts it, and rejects it reversed (`checkStreamFile`, compiled); after the two errata it still
  accepts the corrected script (`spectec_revalidate`).

`generated_metail_fixed_eq` ties the generated `Fixed` script to the errata splice.
-/

public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod

set_option maxRecDepth 100000

/-- The generated original is the elaboration-time import. -/
theorem generated_metail_eq : Scripts.MetaIL.Original.script = Specs.metail := by rfl

/-- The generated fixed script is the errata splice. -/
theorem generated_metail_fixed_eq : Scripts.MetaIL.Fixed.script = metailCorrected := by rfl

spectec_check_stream Specs.metail against "specs/spectec/meta-theory-3a10283c5b/meta-il.ast"

open Silmaril.Wasm.SpecTec.AstText in
/-- The stream as the printer writes it at `--ast-width 80`; `spectec_check_stream` above checks
(compiled) that this is the file's contents. -/
noncomputable def metailText : String := SExp.astFile SExp.defaultWidth (IL.scriptS Specs.metail)

/-- The meta-theory script has no `real` numerals (its `real` occurs only as a type). -/
theorem realsScript_metail : IL.realsScript Specs.metail = [] := by rfl

open Silmaril.Wasm.SpecTec.AstText in
theorem astTextRel_metailText : AstTextRel metailText Specs.metail :=
  astTextRel_astFile _ _ (realsScript_metail ▸ fun _ h => nomatch h)

open Silmaril.Wasm.SpecTec.AstText in
/-- **The verified reader reads the printed meta-theory stream as the imported script.** -/
theorem importAstText?_metailText : importAstText? metailText = some Specs.metail :=
  importAstText?_complete _ _ astTextRel_metailText

end Silmaril.Wasm.SpecTec.Meta

#eval Silmaril.SpecTec.Sem.checkStreamFile "specs/spectec/meta-theory-3a10283c5b/meta-il.ast"

spectec_revalidate Silmaril.Wasm.SpecTec.Meta.metailCorrected
  by Silmaril.Wasm.SpecTec.Meta.metailErrata
  on Silmaril.Wasm.SpecTec.Meta.Specs.metail from "specs/spectec/meta-theory-3a10283c5b/meta-il.ast"
  tying Silmaril.Wasm.SpecTec.Meta.applyErrata_metailErrata
