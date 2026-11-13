module

public import Silmaril.Proofs.Wasm.Models.FXV.Incl
public import Silmaril.Wasm.Models.FXLower.Thms

/-!
# `StepFX'` agrees with `StepFX` on Core code, and is conservative over Core

* `fvals_allCore`: FX values whose code is all Core are Core values (`liftV W`);
* **`step_allCore`**: a `StepFX'` step from code whose instructions are all `core` is a
  `StepFX` step. Only `core`, `seq`, `trapSeq`, `throwSeq`, `invoke` and the `resume_throw`
  rules can apply to such code, and their FX values are then Core values;
* `stepFX'_iff_allCore`: so on such code the two relations coincide;
* `stepFX'_conservativeK`: track H's conservativity, with any continuation store, for
  `StepFX'` (store without FX functions);
* `stepNoK'_iff`, `stepsNoK'_iff`, `divergesNoK'_iff`, **`behavioursFX'_ofCoreK`**: without FX
  functions, the `StepFX'` behaviours of a Core configuration with any continuation store are
  its Core behaviours.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXV

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Proofs.Wasm.Models.FX (isCore map_core_inj)
open Silmaril.Proofs.Wasm.Models.FXLower (ofCoreK)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- FX values whose code is all Core are Core values. -/
theorem fvals_allCore : ∀ {vs : List FVal}, (fvals vs).all isCore = true →
    ∃ W, vs = liftV W
  | [], _ => ⟨[], rfl⟩
  | .val v :: vs, h => by
    simp only [fvals_cons, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨W, rfl⟩ := fvals_allCore h.2
    exact ⟨v :: W, rfl⟩
  | .cont k :: vs, h => by
    simp [FVal.toAdmin, isCore] at h

theorem all_isCore_split {A B C : List AdminFX} (h : (A ++ B ++ C).all isCore = true) :
    A.all isCore = true ∧ B.all isCore = true ∧ C.all isCore = true := by
  simp only [List.all_append, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The value prefix of all-Core code is Core values. -/
theorem allCore_pre {vs : List FVal} {es rest : List AdminFX}
    (hc : (fvals vs ++ es ++ rest).all isCore = true) : ∃ W, vs = liftV W :=
  fvals_allCore (all_isCore_split hc).1

theorem liftV_ne' {W : List Val} {rest : List AdminFX} (h : liftV W ≠ [] ∨ rest ≠ []) :
    W ≠ [] ∨ rest ≠ [] := by
  simpa only [ne_eq, liftV_eq_nil] using h

/-- The `seq` case at Core values. -/
theorem allCore_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {W : List Val} {es es' rest : List AdminFX}
    (h : StepFX P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) (hne : liftV W ≠ [] ∨ rest ≠ []) :
    StepFX P host fx ⟨s, K, f, fvals (liftV W) ++ es ++ rest⟩
      ⟨s', K', f', fvals (liftV W) ++ es' ++ rest⟩ := by
  rw [fvals_liftV]
  exact .seq h (liftV_ne' hne)

/-- **A `StepFX'` step from all-Core code is a `StepFX` step.** -/
theorem step_allCore {x y : ConfigFX H} (h : StepFX' P host fx x y) :
    x.code.all isCore = true → StepFX P host fx x y := by
  induction h with
  | core h => exact fun _ => .core h
  | @seq s s' K K' f f' vs es es' rest h hne ih =>
    intro hc
    obtain ⟨W, rfl⟩ : ∃ W, vs = liftV W := allCore_pre hc
    exact allCore_seq (ih (all_isCore_split hc).2.1) hne
  | trapSeq hne =>
    intro hc
    obtain ⟨W, rfl⟩ : ∃ W, _ = liftV W := allCore_pre hc
    exact fvals_liftV W ▸ .trapSeq (liftV_ne' hne)
  | throwSeq hne =>
    intro hc
    obtain ⟨W, rfl⟩ : ∃ W, _ = liftV W := allCore_pre hc
    exact fvals_liftV W ▸ .throwSeq (liftV_ne' hne)
  | invoke hc hf hcode hfx hn => exact fun _ => .invoke hc hf hcode hfx hn
  | resumeThrow hk ht hr => exact fun _ => .resumeThrow hk ht hr
  | resumeThrowNull => exact fun _ => .resumeThrowNull
  | _ => intro hc; simp [isCore, fvals] at hc

/-- On all-Core code, `StepFX'` and `StepFX` coincide. -/
theorem stepFX'_iff_allCore {x y : ConfigFX H} (hc : x.code.all isCore = true) :
    StepFX' P host fx x y ↔ StepFX P host fx x y :=
  ⟨fun h => step_allCore h hc, stepFX_incl⟩

/-- **Conservativity of `StepFX'` with live continuations.** -/
theorem stepFX'_conservativeK {K : List (Option ContFX)} {c : Config H}
    (hno : NoFX fx c.store) {y : ConfigFX H} :
    StepFX' P host fx (ofCoreK K c) y ↔ ∃ c', Step P (blockFX host fx) c c' ∧ y = ofCoreK K c' := by
  rw [stepFX'_iff_allCore (Silmaril.Proofs.Wasm.Models.FX.all_isCore_map _)]
  exact Silmaril.Wasm.Models.FXLower.stepFX_conservativeK hno

/-- One step without FX functions. -/
theorem stepNoK'_iff {K : List (Option ContFX)} {c : Config H} {y : ConfigFX H} :
    StepFX' P host noFX (ofCoreK K c) y ↔ ∃ c', Step P host c c' ∧ y = ofCoreK K c' := by
  rw [stepFX'_conservativeK (Silmaril.Proofs.Wasm.Models.FX.noFX_store _),
    Silmaril.Wasm.Models.FX.blockFX_noFX]

theorem ofCoreK_inj {K : List (Option ContFX)} {c c' : Config H}
    (h : ofCoreK K c = ofCoreK K c') : c = c' := by
  obtain ⟨s, f, cs⟩ := c
  obtain ⟨s', f', cs'⟩ := c'
  simp only [ofCoreK, ConfigFX.mk.injEq] at h
  obtain ⟨rfl, -, rfl, hc⟩ := h
  rw [map_core_inj hc]

/-- Finite runs without FX functions. -/
theorem stepsNoK'_iff {K : List (Option ContFX)} {c : Config H} {y : ConfigFX H} :
    StepsFX' P host noFX (ofCoreK K c) y ↔ ∃ c', Steps P host c c' ∧ y = ofCoreK K c' := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨c, .refl, rfl⟩
    | tail _ hstep ih =>
      obtain ⟨c₁, hrun, rfl⟩ := ih
      obtain ⟨c₂, hs, rfl⟩ := stepNoK'_iff.mp hstep
      exact ⟨c₂, hrun.tail hs, rfl⟩
  · rintro ⟨c', h, rfl⟩
    induction h with
    | refl => exact .refl
    | tail _ hstep ih => exact ih.tail (stepNoK'_iff.mpr ⟨_, hstep, rfl⟩)

/-- Divergence without FX functions. -/
theorem divergesNoK'_iff {K : List (Option ContFX)} {c : Config H} :
    Silmaril.InfiniteTrace (StepFX' P host noFX) (ofCoreK K c) ↔ Diverges P host c := by
  constructor
  · intro h
    refine Silmaril.InfiniteTrace.of_map (ofCoreK K) (fun _ => True) ?_ trivial h
    intro a b _ hs
    obtain ⟨c', hc, rfl⟩ := stepNoK'_iff.mp hs
    exact ⟨c', hc, trivial, rfl⟩
  · intro h
    exact Silmaril.InfiniteTrace.map (ofCoreK K)
      (fun _ _ hs => stepNoK'_iff.mpr ⟨_, hs, rfl⟩) h

/-- **Without FX functions, the `StepFX'` behaviours of a Core configuration, with any
continuation store, are its Core behaviours.** -/
theorem behavioursFX'_ofCoreK (K : List (Option ContFX)) (c : Config H) :
    behavioursFX' P host noFX (ofCoreK K c) = behavioursOf P host c := by
  ext b
  constructor
  · rintro (⟨d, r, hrun, hcode, rfl⟩ | ⟨rfl, hdiv⟩)
    · obtain ⟨c', hc, rfl⟩ := stepsNoK'_iff.mp hrun
      exact Or.inl ⟨c', r, hc, map_core_inj hcode, rfl⟩
    · exact Or.inr ⟨rfl, divergesNoK'_iff.mp hdiv⟩
  · rintro (⟨c', r, hrun, hcode, rfl⟩ | ⟨rfl, hdiv⟩)
    · exact Or.inl ⟨ofCoreK K c', r, stepsNoK'_iff.mpr ⟨c', hrun, rfl⟩,
        by simp [ofCoreK, hcode], rfl⟩
    · exact Or.inr ⟨rfl, divergesNoK'_iff.mpr hdiv⟩

end Silmaril.Proofs.Wasm.Models.FXV
