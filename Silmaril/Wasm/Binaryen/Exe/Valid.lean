module

public import Silmaril.Wasm.Binaryen.Typing
public import Silmaril.Wasm.Validation.Check.Validate

@[expose] public section

/-! # Validation, checked per run

The pipeline's soundness theorems assume the input is valid (`BModule.Ok m`, i.e.
`∃ t, ModuleOk m.lower t`). The driver discharges that assumption on every run with
Silmaril's executable Core validator `Validation.validate?`
(`Validation/Check/Validate.lean`), whose soundness `validate?_sound` gives
`ModuleOk`. `validOk_sound` packages it for Binaryen modules.

The check is conservative: a module the validator rejects (or does not support) is
passed through unchanged. Completeness of the validator
(`Validation/Check/ValidateComplete.lean`) is not needed for soundness.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen

/-- **The per-run validity check**: Silmaril's Core validator on the lowering. -/
def validOk (m : BModule) : Bool := (Validation.validate? m.lower).isSome

/-- **The validity check is sound.** -/
theorem validOk_sound {m : BModule} (h : validOk m = true) : m.Ok := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp h
  exact ⟨mt, Validation.validate?_sound hmt⟩

end Silmaril.Wasm.Binaryen.Exe
