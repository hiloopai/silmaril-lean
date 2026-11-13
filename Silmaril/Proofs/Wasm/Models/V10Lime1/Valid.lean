module

public import Silmaril.Wasm.Models.V10.Thms

/-!
# Lime1 validity of the 1.0 image is not reflected

`V10.twoResults` (one type with two results) is invalid in 1.0, which has no multi-value; its
Lime1 image is a valid Lime1 module.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V10Lime1

open Silmaril.Wasm

/-- **The Lime1 image of `twoResults` is valid.** -/
theorem twoResults_toLime_valid :
    Silmaril.Wasm.Lime1.Validation.ModuleValid
      Silmaril.Proofs.Wasm.Models.V10.twoResults.toLime := by
  constructor <;>
    simp [Silmaril.Wasm.V1.Module.toLime, Silmaril.Proofs.Wasm.Models.V10.twoResults,
      Silmaril.Wasm.Lime1.Validation.moduleContext,
      Silmaril.Wasm.Lime1.Validation.StartValid, Silmaril.Wasm.Lime1.Validation.FuncTypeValid]

end Silmaril.Proofs.Wasm.Models.V10Lime1
