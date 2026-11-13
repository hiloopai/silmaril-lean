module

public import Silmaril.Raw.Wasm.Unified.FXSim.Bwd

/-!
# CoreFX and Core 3.0 have the same behaviours on FX code that reads as Core code (unrefined)

`behavioursFX_lift`: if FX code `es` reads as Core code `cs` (`LiftAs es cs`), CoreFX without FX
functions and Core 3.0 have the same behaviours from `es` and `cs` (same store and frame, any
continuation store). Results and divergence go forward step by step (`fwd`); backward, a Core
run either is matched step by step (`bwd`) or passes through doomed code, which has no
behaviours (`doomed_behavioursOf`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.Unified.FXSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Unified.Versions
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Forward runs. -/
theorem fwd_steps {x y : ConfigFX H} (h : StepsFX P host noFX x y) {cs : List Admin}
    (hl : LiftAs x.code cs) :
    ∃ cs', Steps P host ⟨x.store, x.frame, cs⟩ ⟨y.store, y.frame, cs'⟩ ∧ LiftAs y.code cs' := by
  induction h with
  | refl => exact ⟨cs, .refl, hl⟩
  | tail _ hst ih =>
    obtain ⟨cs₁, hs₁, hl₁⟩ := ih
    obtain ⟨cs', hst', hl'⟩ := fwd hst cs₁ hl₁
    exact ⟨cs', hs₁.tail hst', hl'⟩

/-- Result code reads only as itself. -/
theorem noStruct_result (r : Result) : ∀ a ∈ r.toAdmin, ¬ Struct a := by
  cases r with
  | values vs => exact noStruct_vals vs
  | throw a => simp [Result.toAdmin, StructI]
  | trap => simp [Result.toAdmin]

/-- Backward runs to a result. -/
theorem bwd_steps {c c' : Config H} (h : Steps P host c c') {r : Result}
    (hr : c'.code = r.toAdmin) :
    ∀ (K : List (Option ContFX)) (es : List AdminFX), LiftAs es c.code →
      ∃ es', StepsFX P host noFX ⟨c.store, K, c.frame, es⟩ ⟨c'.store, K, c'.frame, es'⟩ ∧
        LiftAs es' c'.code := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun K es hl => ⟨es, .refl, hl⟩
  | head hst hrest ih =>
    intro K es hl
    rcases bwd hst hst K es hl with ⟨es₁, hst₁, hl₁⟩ | ⟨d, hd⟩
    · obtain ⟨es', hs', hl'⟩ := ih K es₁ hl₁
      exact ⟨es', Relation.ReflTransGen.head hst₁ hs', hl'⟩
    · rename_i c₁
      obtain ⟨d', hd'⟩ := doomed_steps hrest hd
      exact absurd hr (doomed_not_result hd' r)

/-- **CoreFX and Core 3.0 have the same behaviours on FX code that reads as Core code.** -/
theorem behavioursFX_lift {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {es : List AdminFX} {cs : List Admin} (hl : LiftAs es cs) :
    behavioursFX P host noFX ⟨s, K, f, es⟩ = behavioursOf P host ⟨s, f, cs⟩ := by
  ext b
  constructor
  · rintro (⟨d, r, hst, hc, rfl⟩ | ⟨rfl, hdiv⟩)
    · obtain ⟨cs', hst', hl'⟩ := fwd_steps hst hl
      rw [hc] at hl'
      exact Or.inl ⟨_, r, hst', LiftAs.eq_of_map_core hl', rfl⟩
    · refine Or.inr ⟨rfl, ?_⟩
      refine Silmaril.InfiniteTrace.coinduct
        (fun c : Config H => ∃ x : ConfigFX H, Silmaril.InfiniteTrace (StepFX P host noFX) x ∧
          c = ⟨x.store, x.frame, c.code⟩ ∧ LiftAs x.code c.code) ?_ ⟨⟨s, K, f, es⟩, hdiv, rfl, hl⟩
      rintro c ⟨x, hx, hc, hlx⟩
      obtain ⟨y, hxy, hy⟩ := hx.unfold
      obtain ⟨cs', hst, hl'⟩ := fwd hxy c.code hlx
      refine ⟨⟨y.store, y.frame, cs'⟩, hc ▸ hst, y, hy, rfl, hl'⟩
  · rintro (⟨c', r, hst, hc, rfl⟩ | ⟨rfl, hdiv⟩)
    · obtain ⟨es', hst', hl'⟩ := bwd_steps hst hc K es hl
      rw [hc] at hl'
      exact Or.inl ⟨_, r, hst', LiftAs.eq_map_core hl' (noStruct_result r), rfl⟩
    · refine Or.inr ⟨rfl, ?_⟩
      refine Silmaril.InfiniteTrace.coinduct
        (fun x : ConfigFX H => x.conts = K ∧ ∃ c : Config H, Silmaril.InfiniteTrace (Step P host) c ∧
          c.store = x.store ∧ c.frame = x.frame ∧ LiftAs x.code c.code) ?_
        ⟨rfl, ⟨s, f, cs⟩, hdiv, rfl, rfl, hl⟩
      rintro ⟨xs, xK, xf, xes⟩ ⟨hK, c, hc, hs, hf, hlx⟩
      obtain ⟨c₁, hcc, hc₁⟩ := hc.unfold
      rcases bwd hcc hcc xK xes hlx with ⟨es₁, hst₁, hl₁⟩ | ⟨d, hd⟩
      · refine ⟨⟨c₁.store, xK, c₁.frame, es₁⟩, ?_, hK, c₁, hc₁, rfl, rfl, hl₁⟩
        simp only at hs hf
        rw [← hs, ← hf]
        exact hst₁
      · obtain ⟨s₁, f₁, cs₁⟩ := c₁
        exact absurd hc₁ (doomed_not_diverges (c := ⟨s₁, f₁, cs₁⟩) hd)

end Silmaril.Raw.Wasm.Unified.FXSim
