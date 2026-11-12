module

public import Silmaril.Wasm.Examples.Farkas.Component.Defs
public import Silmaril.Wasm.Examples.Farkas.Thms
public import Silmaril.Wasm.Component.Reference.Sound.Thms

@[expose] public section

/-!
# The Farkas component: the fragment conditions

`farkasS` is in the fragment of `Simple.sound_seq`: `farkasS_good`, `farkasS_floatFree`,
`farkasS_arity` (by `decide`), and `farkasS_inst`: the module's instance is `farkasI`
(`farkasNum_isInst`, from `validate? farkasMod` by `decide +kernel` and the facts about
`farkasRun`). Conversely every instance of the module is `farkasI` (`isInst_eq`). The
reference validator accepts the translation (`farkasS_valid`, `decide +kernel`).
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference

theorem farkasS_good : farkasS.Good :=
  ⟨by decide, by
    intro x hx
    simp only [farkasS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨"row", rfl⟩
    · exact ⟨"entry", rfl⟩
    · exact ⟨"check", rfl⟩⟩

theorem farkasS_floatFree : farkasS.FloatFree := by
  intro x hx
  simp only [farkasS, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem farkasS_arity : farkasS.Arity := by
  intro x hx
  simp only [farkasS, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> decide

/-- The module validates without imports. -/
def validSummary : Bool := (validate? farkasMod).map (·.imports.length) == some 0

theorem validSummary_eq : validSummary = true := by decide +kernel

theorem farkasMod_valid : ∃ mt, validate? farkasMod = some mt ∧ mt.imports = [] := by
  have h : (validate? farkasMod).map (·.imports.length) = some 0 := by
    simpa only [validSummary, beq_iff_eq] using validSummary_eq
  obtain ⟨mt, hmt, hlen⟩ := Option.map_eq_some_iff.mp h
  exact ⟨mt, hmt, List.length_eq_zero_iff.mp hlen⟩

/-- The frame of the instantiation. -/
def farkasFrame : Frame :=
  match farkasRun with
  | some (_, f, _) => f
  | none => {}

theorem farkasFrame_addrs : exportFuncAddrs farkasFrame.module = [0, 1, 2] := rfl

/-- The export addresses have the export types. -/
theorem farkasI_exportTypes :
    List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat, farkasStore.funcs[a]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) [0, 1, 2] farkasExports := by
  obtain ⟨fi₀, fi₁, fi₂, hfs, -, -, -, -, -, -, ht₀, ht₁, ht₂⟩ := farkasStore_funcs
  rw [hfs]
  exact .cons ⟨fi₀, rfl, ht₀⟩ (.cons ⟨fi₁, rfl, ht₁⟩ (.cons ⟨fi₂, rfl, ht₂⟩ .nil))

/-- **`farkasI` is the instance of the checker module.** -/
theorem farkasNum_isInst : farkasNum.IsInst farkasI := by
  obtain ⟨mt, hmt, himp⟩ := farkasMod_valid
  refine ⟨⟨mt, ⟨hmt, ?_, ?_, ⟨farkasFrame, ?_, farkasFrame_addrs⟩, farkasI_exportTypes⟩⟩, rfl, rfl⟩
  · intro xt hxt
    rw [himp] at hxt
    cases hxt
  · rw [himp]
    exact .nil
  · rw [himp]
    exact farkasRun_eq

theorem farkasS_inst : farkasS.Inst := ⟨⟨farkasI, farkasNum_isInst⟩, rfl⟩

/-- **Every instance of the checker module is `farkasI`.** -/
theorem isInst_eq {I : ScalarInstance} (h : farkasNum.IsInst I) : I = farkasI := by
  obtain ⟨⟨mt, hI⟩, himp, hexp⟩ := h
  obtain ⟨mt₀, hmt₀, himp₀⟩ := farkasMod_valid
  have hmt : mt = mt₀ := Option.some.inj (hI.valid.symm.trans hmt₀)
  subst hmt
  obtain ⟨f, hf, hfa⟩ := hI.instantiated
  rw [himp₀] at hf
  have hrun : farkasRun = some (I.store, f, none) := hf
  rw [farkasRun_eq] at hrun
  obtain ⟨hs, hf'⟩ : farkasStore = I.store ∧ farkasFrame = f := by
    simp only [Option.some.injEq, Prod.mk.injEq, and_true] at hrun
    exact hrun
  obtain ⟨imports, exports, addrs, store⟩ := I
  simp only at himp hexp hs hfa
  subst himp hexp hs hf'
  rw [farkasFrame_addrs] at hfa
  subst hfa
  rfl

/-- The validator accepts. -/
def accepts (c : Core3Component) : Bool :=
  match check? Silmaril.Wasm.Component.Features.p2 c with
  | .ok _ => true
  | .error _ => false

theorem exists_of_accepts {c : Core3Component} (h : accepts c = true) :
    ∃ ct, check? Silmaril.Wasm.Component.Features.p2 c = .ok ct := by
  unfold accepts at h
  split at h
  next ct hc => exact ⟨ct, hc⟩
  next => cases h

/-- **The reference validator accepts the component.** -/
theorem farkasS_valid : ∃ ct, check? Silmaril.Wasm.Component.Features.p2 farkasS.toRef = .ok ct :=
  exists_of_accepts (by decide +kernel)

end Silmaril.Wasm.Examples.Farkas
