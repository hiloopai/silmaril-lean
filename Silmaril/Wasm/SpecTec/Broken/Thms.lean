module

public import Silmaril.Wasm.SpecTec.Broken.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Broken.Binary
public import Silmaril.Proofs.Wasm.SpecTec.Broken.Text
public import Silmaril.Proofs.Wasm.SpecTec.Broken.Legacy
public import Silmaril.Proofs.Wasm.SpecTec.Broken.Rules
public import Silmaril.Proofs.Wasm.SpecTec.Broken.Memory

/-!
# SpecTec defects: the generated originals are broken, the generated fixed scripts repaired

All statements are about the generated scripts `Silmaril.Wasm.SpecTec.Scripts.Wasm{10,20,30}`
(`original` and `fixed`).  Each is kernel-checked: grammar facts by transport of
`Equiv/BinaryValues.lean`'s environment-generic theorems, evaluator facts by `rfl` at fuel 100
lifted to every fuel by monotonicity.  The table in `docs/projects/spectec/README.md`
lists each defect with its two theorems.

What the evaluator facts are *not*: the `$utf8` and `Tstringchar` statements are about one
clause's or production's premises under an explicit variable assignment, not about a call of
`$utf8` or a derivation of `Tstringchar` (see `Legacy.lean` and `Text.lean` for why).
-/

public section

namespace Silmaril.Wasm.SpecTec.Broken

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts

/-- **The pinned wasm-3.0 script is broken**, in five independent ways:
`Bi32` is unsigned (#654), `$cont(0x80)` is undefined (#655), the four-byte `$utf8` clause rejects
U+1F601 (#656), the `\u{E000}` escape is rejected (#661), and `BsN(32)` loses `FF 7E` (#803);
also `Step/table.grow-succeed` never fires. -/
theorem wasm30_original_broken :
    Bi32Unsigned Wasm30.original ∧ ContUndefAt80 Wasm30.original ∧
      Utf8RejectsGrin Wasm30.original ∧ EscapeRejectsE000 Wasm30.original ∧
      BsNLosesFF7E Wasm30.original ∧ TableGrowNeverFires Wasm30.original :=
  ⟨bi32Unsigned_original, contUndefAt80_original, utf8RejectsGrin_original,
    escapeRejectsE000_original, bsnLosesFF7E_original, ruleDead_tableGrowSucceed_original⟩

/-- **The fixed wasm-3.0 script repairs #654, #655, #656 and #661.** -/
theorem wasm30_fixed_repairs :
    ¬ Bi32Unsigned Wasm30.fixed ∧ ¬ ContUndefAt80 Wasm30.fixed ∧
      ¬ Utf8RejectsGrin Wasm30.fixed ∧ ¬ EscapeRejectsE000 Wasm30.fixed :=
  ⟨not_bi32Unsigned_fixed, not_contUndefAt80_fixed, not_utf8RejectsGrin_fixed,
    not_escapeRejectsE000_fixed⟩

/-- **…but not #803 or the dead rules**, which no erratum addresses. -/
theorem wasm30_fixed_still_broken :
    BsNLosesFF7E Wasm30.fixed ∧ TableGrowNeverFires Wasm30.fixed :=
  ⟨bsnLosesFF7E_fixed, ruleDead_tableGrowSucceed_fixed⟩

/-- **The pinned wasm-1.0 script is broken** (#684, #685), **and the fixed one repaired.** -/
theorem wasm10_original_broken_fixed_repairs :
    (Utf8RejectsGrin10 Wasm10.original ∧ Utf8AcceptsC2C0 Wasm10.original) ∧
      (¬ Utf8RejectsGrin10 Wasm10.fixed ∧ ¬ Utf8AcceptsC2C0 Wasm10.fixed) :=
  ⟨⟨utf8RejectsGrin10_original, utf8AcceptsC2C0_original⟩,
    ⟨not_utf8RejectsGrin10_fixed, not_utf8AcceptsC2C0_fixed⟩⟩

/-- **The pinned wasm-2.0 script is broken** (#673), **and the fixed one repaired.** -/
theorem wasm20_original_broken_fixed_repairs :
    DataidxMissesNested Wasm20.original ∧ ¬ DataidxMissesNested Wasm20.fixed :=
  ⟨dataidxMissesNested_original, not_dataidxMissesNested_fixed⟩

end Silmaril.Wasm.SpecTec.Broken
