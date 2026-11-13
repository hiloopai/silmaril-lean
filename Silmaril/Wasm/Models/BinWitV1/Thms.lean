module

public import Silmaril.Proofs.Wasm.Models.BinWitV1.Witness

/-!
# 1.0 bytes outside the earlier profiles of the Core 3.0 front end

`BinProfile.not_validC_v1` says that valid 1.0 bytes with an element segment are not `ValidC S`
for any `S` without typed function references (`v10`, `v20`, `lime1`). An earlier step built no 1.0
witness: the copied encoder is Lime1's, and its soundness was stated only at `overlong = true`.

* `encModule_soundW` (in `Silmaril.Proofs.Wasm.Models.BinWitV1`): the copied encoder is sound for
  the strict grammar `EncodesWith false` too, which is the 1.0 grammar on the 1.0 image
  (`v1_iff_lime1`);
* **`wit1_profile`**: `Lime1Bin`'s 22 bytes `witBytes` are a 1.0 encoding of a valid 1.0 module
  (`witMod1`, one table and one element segment), they are `ValidV1` (so a module of `v10Bin`),
  `ValidC v30`, and **not** `ValidC v10`, `ValidC v20` or `ValidC lime1`, while `ValidCR v10`
  (the restatement read up to the legacy forms) holds. So `not_validC_v1` is not vacuous.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.BinWitV1

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Models Silmaril.Wasm.Models.Lime1Bin
open Silmaril.Wasm.Models.BinProfile
open Silmaril.Proofs.Wasm.Models.BinProfile (not_validC_v1 v10_typedFuncRef v20_typedFuncRef
  lime1_typedFuncRef validCR_of_validV1)
open Silmaril.Proofs.Wasm.Models.Lime1Bin (witBytes)
open Silmaril.Proofs.Wasm.Models.BinWitV1 (witMod1 wit1_encodes wit1_valid wit1_validV1)

/-- **The 1.0 witness for `not_validC_v1`.** -/
theorem wit1_profile :
    V1.Binary.Encodes witBytes witMod1 ∧ V1.Validation.ModuleValid witMod1 ∧ witMod1.elems ≠ [] ∧
      ValidV1 witBytes ∧ ValidC v30 witBytes ∧ ¬ ValidC v10 witBytes ∧ ¬ ValidC v20 witBytes ∧
      ¬ ValidC lime1 witBytes ∧ ValidCR v10 witBytes := by
  have hel : witMod1.elems ≠ [] := by simp [witMod1]
  refine ⟨wit1_encodes, wit1_valid, hel, wit1_validV1, ?_, ?_, ?_, ?_, ?_⟩
  · exact validC_of_validL ⟨_, v1_lime1 wit1_encodes, wit1_valid.toLime⟩
  · exact not_validC_v1 v10_typedFuncRef wit1_encodes wit1_valid hel
  · exact not_validC_v1 v20_typedFuncRef wit1_encodes wit1_valid hel
  · exact not_validC_v1 lime1_typedFuncRef wit1_encodes wit1_valid hel
  · exact validCR_of_validV1 wit1_validV1

/-- `witBytes` is a module of `v10Bin` (the binary front end of `v10own`). -/
theorem wit1_v10Bin (H : Type) : (v10Bin H).Valid witBytes := wit1_validV1

end Silmaril.Wasm.Models.BinWitV1

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.Models.BinWitV1.wit1_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Models.BinWitV1.wit1_profile
