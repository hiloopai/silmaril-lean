module

public import Silmaril.Wasm.Models.BinProfile.Defs
public import Silmaril.Wasm.Models.Lime1Mvp.Thms
public import Silmaril.Wasm.Models.V10Mvp.Thms

/-!
# Which bytes the profiles of the Core 3.0 binary front end take

* `elem_toCoreBinary_false`, `not_inFeat_toCoreBinary`: without typed function references, a
  module with an element segment as the 3.0 grammar decodes it (`toCoreBinary`) is not in the
  profile;
* **`not_validC`**, **`not_validC_v1`**: so valid Lime1 bytes, and valid 1.0 bytes, with an
  element segment are **not** valid Core bytes of such a profile (`v10`, `v20`, `lime1`);
* **`validCR_of_validL`**, **`validCR_of_validV1`**: read up to the legacy forms they are:
  valid Lime1 bytes are `ValidCR lime1`, valid 1.0 bytes `ValidCR v10`; `validCR_mono`;
* `wit_profile`: at the 22-byte witness of `Lime1Bin` (a table and an element segment), all of
  it at once.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.BinProfile

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Models Silmaril.Wasm.Models.Lime1Bin
open Silmaril.Wasm.Models.BinProfile
open Silmaril.Proofs.Wasm.Models.Lime1Bin (retype witBytes witMod wit_encodes wit_valid)

variable {S T : FeatureSet}

/-- Without typed function references, `(ref func)` element segments are outside `S`. -/
theorem elem_toCoreBinary_false (hS : S.has .typedFuncRef = false) (e : Lime1.Elem) :
    Elem.inFeatB S e.toCoreBinary = false := by
  simp [Elem.inFeatB, Lime1.Elem.toCoreBinary, RefType.inFeatB, hS]

/-- **A module with an element segment, as Core 3.0 decodes it, is outside `S`.** -/
theorem not_inFeat_toCoreBinary (hS : S.has .typedFuncRef = false) (m : Lime1.Module)
    (hel : m.elems ≠ []) : ¬ Module.InFeat S m.toCoreBinary := by
  intro h
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hel
  have hall : m.toCoreBinary.elems.all (Elem.inFeatB S) = true := by
    simp only [Module.InFeat, Module.inFeatB, Bool.and_eq_true] at h
    exact h.1.1.1.2
  have he' : Lime1.Elem.toCoreBinary e ∈ m.toCoreBinary.elems := by
    simp only [Lime1.Module.toCoreBinary, List.mem_map]
    exact ⟨e, he, rfl⟩
  have := List.all_eq_true.mp hall _ he'
  rw [elem_toCoreBinary_false hS] at this
  exact absurd this (by decide)

/-- **Valid Lime1 bytes with an element segment are not Core bytes of `S`.** -/
theorem not_validC (hS : S.has .typedFuncRef = false) {b : Bytes} {m : Lime1.Module}
    (he : Lime1.Binary.Encodes b m) (hv : Lime1.Validation.ModuleValid m) (hel : m.elems ≠ []) :
    ¬ ValidC S b := by
  rintro ⟨M, hM, -, hin⟩
  have hc : M = m.toCoreBinary := Core.functional hM (lime1_core he hv.binaryCompat)
  exact not_inFeat_toCoreBinary hS m hel (hc ▸ hin)

/-- **Valid 1.0 bytes with an element segment are not Core bytes of `S`.** -/
theorem not_validC_v1 (hS : S.has .typedFuncRef = false) {b : Bytes} {m : V1.Module}
    (he : V1.Binary.Encodes b m) (hv : V1.Validation.ModuleValid m) (hel : m.elems ≠ []) :
    ¬ ValidC S b :=
  not_validC hS (v1_lime1 he) hv.toLime (by simpa [V1.Module.toLime] using hel)

theorem v10_typedFuncRef : v10.has .typedFuncRef = false := by decide
theorem v20_typedFuncRef : v20.has .typedFuncRef = false := by decide
theorem lime1_typedFuncRef : lime1.has .typedFuncRef = false := by decide

/-- `ValidCR` grows with the profile. -/
theorem validCR_mono (h : S ≤ T) {b : Bytes} (hb : ValidCR S b) : ValidCR T b := by
  obtain ⟨M, hM, hv, hin⟩ := hb
  exact ⟨M, hM, hv, Lime1Mvp.inFeatM_mono h hin⟩

/-- The retyped decoding of valid Lime1 bytes is the Core image `toCore`. -/
theorem retype_decode {b : Bytes} {m : Lime1.Module} (he : Lime1.Binary.Encodes b m)
    (hv : Lime1.Validation.ModuleValid m) :
    Core.Encodes b m.toCoreBinary ∧ retype m.toCoreBinary = m.toCore := by
  refine ⟨lime1_core he hv.binaryCompat, ?_⟩
  have h := square_retype he hv
  rw [(square he hv).2, Option.map_some] at h
  exact Option.some.inj h

/-- **Valid Lime1 bytes are Core bytes of `lime1` up to the legacy forms.** -/
theorem validCR_of_validL {b : Bytes} (h : ValidL b) : ValidCR lime1 b := by
  obtain ⟨m, he, hv⟩ := h
  obtain ⟨hc, hr⟩ := retype_decode he hv
  exact ⟨m.toCoreBinary, hc, hr ▸ Lime1Mvp.validInM_lime1 hv⟩

/-- **Valid 1.0 bytes are Core bytes of `v10` up to the legacy forms.** -/
theorem validCR_of_validV1 {b : Bytes} (h : ValidV1 b) : ValidCR v10 b := by
  obtain ⟨m, he, hv, -⟩ := h
  obtain ⟨hc, hr⟩ := retype_decode (v1_lime1 he) hv.toLime
  refine ⟨m.toLime.toCoreBinary, hc, ?_⟩
  rw [hr]
  refine ⟨Lime1.Validation.ModuleValid.toCore hv.toLime, ?_⟩
  rw [V1.Module.toLime_toCore]
  exact Silmaril.Wasm.Models.V10Mvp.v10_inFeatM hv

/-- **The profiles at the witness**: `witBytes` are valid Lime1 bytes and valid Core bytes of
`v30`, not valid Core bytes of `v10`, `v20` or `lime1`, and `ValidCR lime1`. -/
theorem wit_profile :
    ValidL witBytes ∧ ValidC v30 witBytes ∧ ¬ ValidC v10 witBytes ∧ ¬ ValidC v20 witBytes ∧
      ¬ ValidC lime1 witBytes ∧ ValidCR lime1 witBytes := by
  have hL : ValidL witBytes := ⟨witMod, wit_encodes, wit_valid⟩
  have hel : witMod.elems ≠ [] := by simp [witMod]
  exact ⟨hL, validC_of_validL hL, not_validC v10_typedFuncRef wit_encodes wit_valid hel,
    not_validC v20_typedFuncRef wit_encodes wit_valid hel,
    not_validC lime1_typedFuncRef wit_encodes wit_valid hel, validCR_of_validL hL⟩

end Silmaril.Proofs.Wasm.Models.BinProfile
