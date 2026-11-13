module

public import Silmaril.Proofs.Wasm.Models.FX.Conservative
public import Silmaril.Wasm.Behaviour.Semantics.V3

/-!
# CoreFX is conservative over Core 3.0: runs, divergence and behaviours

Without FX functions (`noFX`):

* `stepNo_iff`: the FX steps of a Core configuration are exactly the images of its Core steps;
* `stepsFX_iff`: so are its finite runs;
* `divergesFX_iff`: it diverges in CoreFX iff it diverges in Core;
* `behavioursFX_ofCore`: its CoreFX behaviours are its Core behaviours.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **One step**: without FX functions, FX steps of Core configurations are Core steps. -/
theorem stepNo_iff {c : Config H} {y : ConfigFX H} :
    StepFX P host noFX (ofCore c) y ↔ ∃ c', Step P host c c' ∧ y = ofCore c' := by
  constructor
  · intro h
    obtain ⟨c', hs, hy⟩ := step_ofCore h c rfl (noFX_store _)
    rw [blockFX_noFX] at hs
    exact ⟨c', hs, hy⟩
  · rintro ⟨c', hs, rfl⟩
    rw [← blockFX_noFX host] at hs
    exact ofCore_step hs

theorem ofCore_injective : Function.Injective (ofCore (H := H)) := by
  intro c c' h
  obtain ⟨s, f, cs⟩ := c
  obtain ⟨s', f', cs'⟩ := c'
  simp only [ofCore, ConfigFX.mk.injEq] at h
  obtain ⟨rfl, -, rfl, hc⟩ := h
  rw [map_core_inj hc]

/-- Finite FX runs of a Core configuration are images of Core runs. -/
theorem stepsFX_ofCore {c : Config H} {y : ConfigFX H}
    (h : StepsFX P host noFX (ofCore c) y) : ∃ c', Steps P host c c' ∧ y = ofCore c' := by
  induction h with
  | refl => exact ⟨c, .refl, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨c₁, hrun, rfl⟩ := ih
    obtain ⟨c₂, hs, rfl⟩ := stepNo_iff.mp hstep
    exact ⟨c₂, hrun.tail hs, rfl⟩

/-- Core runs lift. -/
theorem ofCore_steps {c c' : Config H} (h : Steps P host c c') :
    StepsFX P host noFX (ofCore c) (ofCore c') := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (stepNo_iff.mpr ⟨_, hstep, rfl⟩)

/-- **Finite runs**: the FX runs of a Core configuration are exactly the images of its Core
runs. -/
theorem stepsFX_iff {c : Config H} {y : ConfigFX H} :
    StepsFX P host noFX (ofCore c) y ↔ ∃ c', Steps P host c c' ∧ y = ofCore c' :=
  ⟨stepsFX_ofCore, fun ⟨_, h, hy⟩ => hy ▸ ofCore_steps h⟩

/-- Every point of an FX trace from a Core configuration is a Core configuration. -/
theorem trace_core {c : Config H} {T : Nat → ConfigFX H} (h0 : T 0 = ofCore c)
    (hT : ∀ n, StepFX P host noFX (T n) (T (n + 1))) : ∀ n, ∃ c', T n = ofCore c'
  | 0 => ⟨c, h0⟩
  | n + 1 => by
    obtain ⟨cn, hn⟩ := trace_core h0 hT n
    have hs := hT n
    rw [hn] at hs
    obtain ⟨c', -, hc'⟩ := stepNo_iff.mp hs
    exact ⟨c', hc'⟩

/-- **Divergence**: a Core configuration diverges in CoreFX iff it diverges in Core. -/
theorem divergesFX_iff {c : Config H} :
    Silmaril.InfiniteTrace (StepFX P host noFX) (ofCore c) ↔ Diverges P host c := by
  constructor
  · rintro ⟨T, h0, hT⟩
    have hc := trace_core h0 hT
    choose g hg using hc
    refine ⟨g, ofCore_injective (by rw [← hg 0, h0]), fun n => ?_⟩
    have hs := hT n
    rw [hg n, hg (n + 1)] at hs
    obtain ⟨c', hstep, he⟩ := stepNo_iff.mp hs
    rw [ofCore_injective he]
    exact hstep
  · rintro ⟨T, h0, hT⟩
    exact ⟨fun n => ofCore (T n), by simp only [h0], fun n => stepNo_iff.mpr ⟨_, hT n, rfl⟩⟩

/-- **Behaviours**: the CoreFX behaviours of a Core configuration are its Core behaviours. -/
theorem behavioursFX_ofCore (c : Config H) :
    behavioursFX P host noFX (ofCore c) = behavioursOf P host c := by
  ext b
  constructor
  · rintro (⟨d, r, hrun, hcode, rfl⟩ | ⟨rfl, hdiv⟩)
    · obtain ⟨c', hc, rfl⟩ := stepsFX_ofCore hrun
      exact Or.inl ⟨c', r, hc, map_core_inj hcode, rfl⟩
    · exact Or.inr ⟨rfl, divergesFX_iff.mp hdiv⟩
  · rintro (⟨c', r, hrun, hcode, rfl⟩ | ⟨rfl, hdiv⟩)
    · exact Or.inl ⟨ofCore c', r, ofCore_steps hrun, by simp [ofCore, hcode], rfl⟩
    · exact Or.inr ⟨rfl, divergesFX_iff.mpr hdiv⟩

end Silmaril.Proofs.Wasm.Models.FX
