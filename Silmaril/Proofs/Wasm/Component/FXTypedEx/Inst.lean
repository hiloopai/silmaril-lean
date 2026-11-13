module

public import Silmaril.Wasm.Component.FXTypedEx.Defs
public import Silmaril.Wasm.Component.Reference.Litmus.Thms

/-!
# Components with FX functions for `SimpleFX.Typed`: the fragment conditions

* `tInst_isInst`: `tInst` is the instance of `tNum` (kernel evaluation of `validate?` and
  `instantiateOnce?` on a Boolean summary, `decide +kernel`; no native evaluation);
* for `susC`, `mixC` and `badC`: `Good`, `FloatFree`, `Inst` and `Arity` of the IR component;
  for `susC` and `mixC`: the typed fragment `SimpleFX.Frag` (for `mixC`, the adder's module is in
  the split fragment, `binCore3_splitOk`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXTypedEx

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.FXEngine
open Silmaril.Wasm.Component.FXRefV Silmaril.Wasm.Component.FXTyped Silmaril.Wasm.Component.FXTypedEx
open Silmaril.Wasm.Component.FXSuspend (tMod susDecl runDecl)

/-! ## The instance of `tMod` -/

/-- The Boolean summary of the instantiation of `tMod`. -/
def tSummary : Bool :=
  ((validate? tMod).map (·.imports.length) == some 0) &&
    match instantiateOnce? (Silmaril.Wasm.Game.importStore []) tMod [] with
    | some (_, f, none) => Silmaril.Wasm.Game.exportFuncAddrs f.module == []
    | _ => false

theorem tSummary_eq : tSummary = true := by decide +kernel

theorem tFacts : (∃ mt, validate? tMod = some mt ∧ mt.imports = []) ∧
    ∃ f : Frame, instantiateOnce? (Silmaril.Wasm.Game.importStore []) tMod [] = some (tStore, f, none) ∧
      Silmaril.Wasm.Game.exportFuncAddrs f.module = [] := by
  have h := tSummary_eq
  simp only [tSummary, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨mt, hmt, hlen⟩ := Option.map_eq_some_iff.mp h₁
  refine ⟨⟨mt, hmt, List.length_eq_zero_iff.mp hlen⟩, ?_⟩
  unfold tStore
  rcases e : instantiateOnce? (Silmaril.Wasm.Game.importStore []) tMod [] with _ | ⟨s, f, st⟩
  · rw [e] at h₂
    cases h₂
  · rw [e] at h₂
    cases st with
    | none => exact ⟨f, rfl, by simpa using h₂⟩
    | some _ => cases h₂

/-- **`tInst` is the instance of `tNum`.** -/
theorem tInst_isInst : tNum.IsInst tInst := by
  obtain ⟨⟨mt, hmt, himp⟩, ⟨f, hf, hfa⟩⟩ := tFacts
  refine ⟨⟨mt, ⟨hmt, ?_, ?_, ?_, .nil⟩⟩, rfl, rfl⟩
  · intro xt hxt
    rw [himp] at hxt
    cases hxt
  · rw [himp]
    exact .nil
  · refine ⟨f, ?_, hfa⟩
    rw [himp]
    exact hf

/-- `tNum` is instantiated as the IR assumes. -/
theorem tNum_inst : Simple.Inst ⟨tNum, []⟩ := ⟨⟨tInst, tInst_isInst⟩, rfl⟩

/-! ## `susC` -/

theorem susC_good : susC.toSimple.Good :=
  ⟨by decide, by
    intro x hx
    simp only [susC, SimpleFX.toSimple, List.mem_singleton] at hx
    subst hx
    exact ⟨"run", rfl⟩⟩

theorem susC_floatFree : susC.toSimple.FloatFree := by
  intro x hx
  simp only [susC, SimpleFX.toSimple, List.mem_singleton] at hx
  subst hx
  exact ⟨rfl, rfl⟩

theorem susC_inst : susC.Inst :=
  ⟨tNum_inst, by decide, by intro d _; simp [susC, tNum, tMod]⟩

theorem susC_arity : susC.toSimple.Arity := by
  intro x hx
  simp only [susC, SimpleFX.toSimple, List.mem_singleton] at hx
  subst hx
  decide

theorem susC_frag : SimpleFX.Frag susC where
  core x hx hk := by
    simp only [susC, List.mem_singleton] at hx
    subst hx
    simp [susC, tNum] at hk
  fx x hx _ := by
    simp only [susC, List.mem_singleton] at hx
    subst hx
    rfl

/-! ## `mixC` -/

/-- The adder's module is in the split fragment. -/
theorem binCore3_splitOk : Linked2.ModSplitOk (Litmus.binCore3 .add) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mixC_good : mixC.toSimple.Good :=
  ⟨by decide, by
    intro x hx
    simp only [mixC, SimpleFX.toSimple, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨"f", rfl⟩
    · exact ⟨"go", rfl⟩⟩

theorem mixC_floatFree : mixC.toSimple.FloatFree := by
  intro x hx
  simp only [mixC, SimpleFX.toSimple, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem mixC_inst : mixC.Inst :=
  ⟨⟨Litmus.adderS_inst.inst, Litmus.adderS_inst.names⟩, by decide, by
    intro d hd
    simp only [mixC, List.mem_singleton] at hd
    subst hd
    decide⟩

theorem mixC_arity : mixC.toSimple.Arity := by
  intro x hx
  simp only [mixC, SimpleFX.toSimple, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl <;> decide

theorem mixC_frag : SimpleFX.Frag mixC where
  core _ _ _ := binCore3_splitOk
  fx x hx hk := by
    simp only [mixC, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simp [mixC, Litmus.binMod] at hk
    · rfl

/-! ## `badC` -/

theorem badC_good : badC.toSimple.Good :=
  ⟨by decide, by
    intro x hx
    simp only [badC, SimpleFX.toSimple, List.mem_singleton] at hx
    subst hx
    exact ⟨"bad", rfl⟩⟩

theorem badC_floatFree : badC.toSimple.FloatFree := by
  intro x hx
  simp only [badC, SimpleFX.toSimple, List.mem_singleton] at hx
  subst hx
  exact ⟨rfl, rfl⟩

theorem badC_inst : badC.Inst :=
  ⟨tNum_inst, by decide, by intro d _; simp [badC, tNum, tMod]⟩

theorem badC_arity : badC.toSimple.Arity := by
  intro x hx
  simp only [badC, SimpleFX.toSimple, List.mem_singleton] at hx
  subst hx
  decide

end Silmaril.Proofs.Wasm.Component.FXTypedEx
