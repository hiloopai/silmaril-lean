module

public import Silmaril.Wasm.Tools.Gen.Cmd.Norm.Defs
public import Silmaril.Wasm.Tools.Gen.Core.Thms

/-!
# Validity up to the Wasm 1.0 spellings: specification

* `validInWB_iff`: `validInWB S` decides `ValidInW S`;
* `inFeat_wnorm`, `validIn_validInW`: a module valid in `S` is valid in `S` up to the
  spellings (`wnorm` only removes features);
* `checkedGenW_validInW`: the checked generator's outputs are `ValidInW S`.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd

open Silmaril.Wasm Silmaril.Wasm.Models

theorem validInWB_iff {S : FeatureSet} {m : Module} : validInWB S m = true ↔ ValidInW S m := by
  simp only [validInWB, Bool.and_eq_true, ValidInW, Module.InFeat]
  rw [Silmaril.Wasm.Perf.ValidateR.validateR_eq, Validation.validate?_isSome_iff]

theorem constExprB_nil (S : FeatureSet) : constExprB S [] = true := by
  have h1 : Instr.insInFeatB S [] = true := insInFeatB_iff.mpr fun _ hi => nomatch hi
  have h2 : simpleConst [] = true := rfl
  simp only [constExprB, h1, h2, Bool.true_or, Bool.and_self]

theorem table_wnorm {S : FeatureSet} {t : Table} (h : Table.inFeatB S t = true) :
    Table.inFeatB S (if implicitInit t then { t with init := [] } else t) = true := by
  split
  · have h' : TableType.inFeatB S t.type = true := by
      simp only [Table.inFeatB, Bool.and_eq_true] at h
      exact h.1
    simp [Table.inFeatB, h', constExprB_nil]
  · exact h

theorem elem_wnorm {S : FeatureSet} {e : Elem} (h : Elem.inFeatB S e = true) :
    Elem.inFeatB S (if funcIdxElem e then
      { e with type := ⟨true, .abstract .func⟩, init := e.init.map fun _ => [] } else e) = true := by
  split
  · have hm : ElemMode.inFeatB S e.mode = true := by
      simp only [Elem.inFeatB, Bool.and_eq_true] at h
      exact h.2
    simp [Elem.inFeatB, hm, constExprB_nil]
  · exact h

/-- `wnorm` only removes features. -/
theorem inFeat_wnorm {S : FeatureSet} {m : Module} (h : Module.InFeat S m) :
    Module.InFeat S (wnorm m) := by
  unfold Module.InFeat Module.inFeatB at *
  have ht : (m.tables.map fun t => if implicitInit t then { t with init := [] } else t).all
      (Table.inFeatB S) = true := by
    simp only [Bool.and_eq_true] at h
    rw [List.all_map, List.all_eq_true]
    intro t ht
    exact table_wnorm (List.all_eq_true.mp h.1.1.1.1.1.2 t ht)
  have he : (m.elems.map fun e => if funcIdxElem e then
      { e with type := ⟨true, .abstract .func⟩, init := e.init.map fun _ => [] } else e).all
      (Elem.inFeatB S) = true := by
    simp only [Bool.and_eq_true] at h
    rw [List.all_map, List.all_eq_true]
    intro e he
    exact elem_wnorm (List.all_eq_true.mp h.1.1.1.2 e he)
  simp only [Bool.and_eq_true] at h
  simp only [wnorm, Bool.and_eq_true, List.length_map]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.2⟩, h.1.1.1.1.1.1.1.1.2⟩,
    h.1.1.1.1.1.1.1.2⟩, h.1.1.1.1.1.1.2⟩, ht⟩, h.1.1.1.1.2⟩, he⟩,
    h.1.1.2⟩, h.1.2⟩, h.2⟩

theorem validIn_validInW {S : FeatureSet} {m : Module} (h : ValidIn S m) : ValidInW S m :=
  ⟨h.1, inFeat_wnorm h.2⟩

theorem emptyModule_validInW (S : FeatureSet) : ValidInW S ({} : Module) :=
  validIn_validInW (Core.empty_validIn S)

theorem checkedGenW_validInW (S : FeatureSet) (raw : ByteArray → Module) (seed : ByteArray) :
    ValidInW S (checkedGenW S raw seed) := by
  unfold checkedGenW
  split
  · exact validInWB_iff.mp ‹_›
  · exact emptyModule_validInW S

theorem checkedGenW_of_valid {S : FeatureSet} {raw : ByteArray → Module} {seed : ByteArray}
    (h : validInWB S (raw seed) = true) : checkedGenW S raw seed = raw seed := by
  simp [checkedGenW, h]

end Silmaril.Wasm.Tools.Gen.Cmd
