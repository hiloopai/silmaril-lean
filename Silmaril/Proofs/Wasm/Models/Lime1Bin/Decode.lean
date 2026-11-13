module

public import Silmaril.Wasm.Models.Lime1Bin.Defs

/-!
# Binary front ends: decodings, validity and the decoding square

* `decodeL_eq`, `decodeC_eq`, `decodeV1_eq`: a byte string that encodes a module decodes to it
  (the grammars are functional);
* `inFeat_toCoreBinary`: the binary-faithful Core image of a Lime1 module is in `v30`, as the
  image `toCore` is (`module_inFeat_v30`): the two differ only in element types, and `(ref func)`
  is a reference type of `v30`;
* `validC_of_validL`: **valid Lime1 bytes are valid Core 3.0 bytes of `v30`, the same bytes**;
* `square`: for a valid Lime1 module `m` with encoding `b`, Lime1 decodes `b` to `m` and Core
  3.0 decodes `b` to `m.toCoreBinary`; `square_retype`: retyping the element segments of Core's
  decoding to `funcref` gives `m.toCore`, the module map of `lime1Emb`;
* `decodeC_ne_toCore`: with an element segment, Core's decoding is **not** `m.toCore`;
* `validL_of_validV1`, `decodeL_of_v1`: valid 1.0 bytes are valid Lime1 bytes, decoding to
  `m.toLime`; `validC_of_validV1`: they are valid Core 3.0 bytes of `v30`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Lime1Bin

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Models Silmaril.Wasm.Models.Lime1Bin

/-! ## Decodings -/

theorem decodeL_eq {b : Bytes} {m : Lime1.Module} (h : Lime1.Binary.Encodes b m) :
    decodeL b = some m := by
  have hex : ∃ m, Lime1.Binary.Encodes b m := ⟨m, h⟩
  have hc : hex.choose = m := Lime1.Binary.functional hex.choose_spec h
  unfold decodeL
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact congrArg some hc

theorem decodeC_eq {b : Bytes} {M : Silmaril.Wasm.Module} (h : Core.Encodes b M) :
    decodeC b = some M := by
  have hex : ∃ M, Core.Encodes b M := ⟨M, h⟩
  have hc : hex.choose = M := Core.functional hex.choose_spec h
  unfold decodeC
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact congrArg some hc

theorem decodeV1_eq {b : Bytes} {m : V1.Module} (h : V1.Binary.Encodes b m) :
    decodeV1 b = some m := by
  have hex : ∃ m, V1.Binary.Encodes b m := ⟨m, h⟩
  have hc : hex.choose = m := V1.Binary.functional hex.choose_spec h
  unfold decodeV1
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact congrArg some hc

/-- A byte string decodes in Lime1 exactly when it encodes the decoding. -/
theorem decodeL_eq_some_iff {b : Bytes} {m : Lime1.Module} :
    decodeL b = some m ↔ Lime1.Binary.Encodes b m := by
  refine ⟨fun h => ?_, decodeL_eq⟩
  by_cases hex : ∃ m, Lime1.Binary.Encodes b m
  · obtain ⟨m', hm'⟩ := hex
    have he : some m' = some m := (decodeL_eq hm').symm.trans h
    exact Option.some.inj he ▸ hm'
  · have hn : decodeL b = none := by unfold decodeL; rw [dite_eq_right_of_eq_false (eq_false hex)]
    rw [hn] at h
    exact absurd h (by simp)

/-! ## Feature membership of the binary-faithful image -/

/-- `(ref func)` is a reference type of `v30`. -/
theorem refFunc_v30 : RefType.inFeatB v30 ⟨false, .abstract .func⟩ = true := by decide

/-- The element segments of the two images have the same feature membership in `v30`. -/
theorem elem_inFeat (e : Lime1.Elem) :
    Elem.inFeatB v30 e.toCoreBinary = Elem.inFeatB v30 e.toCore := by
  simp [Elem.inFeatB, Lime1.Elem.toCoreBinary, refFunc_v30]
  rfl

/-- **The binary-faithful Core image of a Lime1 module is in `v30`.** -/
theorem inFeat_toCoreBinary (m : Lime1.Module) : Module.InFeat v30 m.toCoreBinary := by
  have h : Module.InFeat v30 m.toCore := Silmaril.Proofs.Wasm.Models.Lime1Core.module_inFeat_v30 m
  have he : m.toCoreBinary.elems.all (Elem.inFeatB v30) = m.toCore.elems.all (Elem.inFeatB v30) := by
    simp only [Lime1.Module.toCoreBinary, Lime1.Module.toCore, List.all_map, Function.comp_def,
      elem_inFeat]
  have hm : Module.inFeatB v30 m.toCoreBinary = Module.inFeatB v30 m.toCore := by
    simp only [Module.inFeatB, he]
    rfl
  exact hm.trans h

/-! ## Validity of bytes -/

/-- **Valid Lime1 bytes are valid Core 3.0 bytes of `v30`.** -/
theorem validC_of_validL {b : Bytes} (h : ValidL b) : ValidC v30 b := by
  obtain ⟨m, he, hv⟩ := h
  exact ⟨m.toCoreBinary, lime1_core he hv.binaryCompat,
    hv.toCoreBinary, inFeat_toCoreBinary m⟩

/-- **The decoding square**: Lime1 decodes the bytes of a valid module to the module, Core 3.0
to its binary-faithful image. -/
theorem square {b : Bytes} {m : Lime1.Module} (he : Lime1.Binary.Encodes b m)
    (hv : Lime1.Validation.ModuleValid m) :
    decodeL b = some m ∧ decodeC b = some m.toCoreBinary :=
  ⟨decodeL_eq he, decodeC_eq (lime1_core he hv.binaryCompat)⟩

/-- Element segments retyped to `funcref`. -/
def retype (M : Silmaril.Wasm.Module) : Silmaril.Wasm.Module :=
  { M with elems := M.elems.map fun e => { e with type := V1.funcref } }

/-- **Retyping Core's decoding gives `toCore`**, the module map of `lime1Emb`. -/
theorem square_retype {b : Bytes} {m : Lime1.Module} (he : Lime1.Binary.Encodes b m)
    (hv : Lime1.Validation.ModuleValid m) : (decodeC b).map retype = some m.toCore := by
  rw [(square he hv).2, Option.map_some, Lime1.Module.toCore_eq_retype]
  rfl

/-- **With an element segment, Core 3.0 does not decode the bytes to `toCore`.** -/
theorem decodeC_ne_toCore {b : Bytes} {m : Lime1.Module} (he : Lime1.Binary.Encodes b m)
    (hv : Lime1.Validation.ModuleValid m) (hel : m.elems ≠ []) :
    decodeC b ≠ some m.toCore := fun h =>
  lime1_core_toCore_counterexample he hv.binaryCompat hel (decodeC_eq_some h)
where
  decodeC_eq_some {b : Bytes} {M : Silmaril.Wasm.Module} (h : decodeC b = some M) :
      Core.Encodes b M := by
    by_cases hex : ∃ M, Core.Encodes b M
    · obtain ⟨M', hM'⟩ := hex
      have h' : some M' = some M := (decodeC_eq hM').symm.trans h
      exact Option.some.inj h' ▸ hM'
    · have hn : decodeC b = none := by unfold decodeC; rw [dite_eq_right_of_eq_false (eq_false hex)]
      rw [hn] at h
      exact absurd h (by simp)

/-! ## 1.0 bytes -/

/-- **Valid 1.0 bytes are valid Lime1 bytes**, of the module's Lime1 image. -/
theorem validL_of_validV1 {b : Bytes} (h : ValidV1 b) : ValidL b := by
  obtain ⟨m, he, hv, -⟩ := h
  exact ⟨m.toLime, v1_lime1 he, hv.toLime⟩

/-- Lime1 decodes 1.0 bytes to the Lime1 image. -/
theorem decodeL_of_v1 {b : Bytes} {m : V1.Module} (he : V1.Binary.Encodes b m) :
    decodeL b = some m.toLime :=
  decodeL_eq (v1_lime1 he)

/-- **Valid 1.0 bytes are valid Core 3.0 bytes of `v30`.** -/
theorem validC_of_validV1 {b : Bytes} (h : ValidV1 b) : ValidC v30 b :=
  validC_of_validL (validL_of_validV1 h)

end Silmaril.Proofs.Wasm.Models.Lime1Bin
