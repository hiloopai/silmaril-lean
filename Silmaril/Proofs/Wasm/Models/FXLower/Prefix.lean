module

public import Silmaril.Proofs.Wasm.Models.FXLower.SrcInv
public import Silmaril.Proofs.Wasm.Models.FXLower.HandlerEq

/-!
# Values in front of a handler frame commute into it (no host calls, no FX functions)

`underHW K hs W c` is Core code `c` under a handler frame, after the values `W`. Its CoreFX
behaviours are Core behaviours of `vals W ++ c` (`withVals W c`). This is the commutation that
`resume`'s untyped split of the operand stack needs: the values that `resume` leaves outside its
handler frame can be moved back in.

* `step_underHW`: a step of `underHW K hs W c` is a Core step of `c`, the frame returning a
  result of `c` (leaving `vals W ++ result`), or a `br`/`return` escaping the frame (stuck);
* `runs_ofCoreK`, `step_of_traceK`: runs and infinite traces of Core code with live
  continuations are Core runs and Core steps;
* `runs_underHW`, `diverges_underHW`: runs and divergence of `underHW K hs W c` are Core runs
  and divergence of `withVals W c`;
* **`behaviours_underHW`**: the CoreFX behaviours of `underHW K hs W c` are Core behaviours of
  `withVals W c`.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXLower

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXLower
open Silmaril.Proofs.Wasm.Models.FX (isCore map_core_inj all_isCore_map noFX_store)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- Core code under a handler frame, after the values `W`. -/
def underHW (K : List (Option ContFX)) (hs : List HClause) (W : List Val) (c : Config H) :
    ConfigFX H :=
  ⟨c.store, K, c.frame, cvals W ++ onHandler hs c.code⟩

/-- The Core configuration `vals W ++ c`. -/
def withVals (W : List Val) (c : Config H) : Config H := ⟨c.store, c.frame, vals W ++ c.code⟩

theorem underHW_nil (K : List (Option ContFX)) (hs : List HClause) (c : Config H) :
    underHW K hs [] c = underH K hs c := rfl

theorem withVals_nil (c : Config H) : withVals [] c = c := rfl

/-- **Values in front of a Core step.** -/
theorem lift_vals {host : HostSemantics H} (W : List Val) {c c' : Config H}
    (h : Step P host c c') : Step P host (withVals W c) (withVals W c') := by
  by_cases hW : W = []
  · subst hW
    exact h
  · obtain ⟨s, f, cs⟩ := c
    obtain ⟨s', f', cs'⟩ := c'
    have h' : Step P host ⟨s, f, vals W ++ cs ++ []⟩ ⟨s', f', vals W ++ cs' ++ []⟩ :=
      Step.ctxtInstrs h (Or.inl hW)
    show Step P host ⟨s, f, vals W ++ cs⟩ ⟨s', f', vals W ++ cs'⟩
    simpa only [List.append_nil] using h'

theorem ofCoreK_withVals (K : List (Option ContFX)) (W : List Val) (c : Config H) :
    ofCoreK K (withVals W c) = ⟨c.store, K, c.frame, cvals W ++ c.code.map .core⟩ := by
  simp [ofCoreK, withVals, cvals]

/-- What a step of `underHW K hs W c` can do. -/
abbrev UnderHWStep (K : List (Option ContFX)) (hs : List HClause) (W : List Val) (c : Config H)
    (y : ConfigFX H) : Prop :=
  (∃ c', Step P noHost c c' ∧ y = underHW K hs W c') ∨
  (∃ r : Result, c.code = r.toAdmin ∧ y = ofCoreK K (withVals W c)) ∨
  (∃ (vs : List Val) (X : Admin), Escapes X ∧
    y = ofCoreK K ⟨c.store, c.frame, vals (W ++ vs) ++ [X]⟩)

/-- Prefixing values maps a handler-frame step to an `underHW` step. -/
theorem underHWStep_of {K : List (Option ContFX)} {hs : List HClause} {W : List Val}
    {c : Config H} {y' : ConfigFX H} (h : UnderHStep (P := P) K hs c y') :
    UnderHWStep (P := P) K hs W c ⟨y'.store, y'.conts, y'.frame, cvals W ++ y'.code⟩ := by
  rcases h with ⟨c', hst, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨vs, X, -, hX, -, rfl⟩
  · exact Or.inl ⟨c', hst, rfl⟩
  · exact Or.inr (Or.inl ⟨r, hr, (ofCoreK_withVals K W c).symm⟩)
  · exact Or.inr (Or.inr ⟨vs, X, hX, by simp [ofCoreK, cvals]⟩)

/-- **Inversion of a step of `underHW`.** -/
theorem step_underHW {K : List (Option ContFX)} {hs : List HClause} {W : List Val}
    {c : Config H} {y : ConfigFX H} (h : StepFX P noHost noFX (underHW K hs W c) y) :
    UnderHWStep (P := P) K hs W c y := by
  by_cases hW : W = []
  · subst hW
    have h1 : UnderHWStep (P := P) K hs [] c ⟨y.store, y.conts, y.frame, cvals [] ++ y.code⟩ :=
      underHWStep_of (step_underH h)
    exact h1
  · obtain ⟨y', hy', rfl⟩ := step_prefixHandler h W hs (c.code.map .core) hW rfl
    exact underHWStep_of (step_underH hy')

theorem underHW_not_result {K : List (Option ContFX)} {hs : List HClause} {W : List Val}
    {c : Config H} (r : Result) : (underHW K hs W c).code ≠ r.toAdmin.map .core := by
  intro h
  have h1 : (r.toAdmin.map AdminFX.core).all isCore = true := all_isCore_map _
  rw [← h] at h1
  simp [underHW, onHandler, isCore] at h1

theorem underHW_injective {K : List (Option ContFX)} {hs : List HClause} {W : List Val}
    {c c' : Config H} (h : underHW K hs W c = underHW K hs W c') : c = c' := by
  obtain ⟨s, f, cs⟩ := c
  obtain ⟨s', f', cs'⟩ := c'
  simp only [underHW, onHandler, ConfigFX.mk.injEq, List.append_cancel_left_eq,
    List.cons.injEq, AdminFX.handler.injEq, true_and, and_true] at h
  obtain ⟨rfl, rfl, hc⟩ := h
  rw [map_core_inj hc]

/-- **Runs of Core code with live continuations are Core runs.** -/
theorem runs_ofCoreK {K : List (Option ContFX)} {x d : ConfigFX H}
    (hrun : StepsFX P noHost noFX x d) :
    ∀ c, x = ofCoreK K c → ∃ c', Steps P noHost c c' ∧ d = ofCoreK K c' := by
  induction hrun using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun c hx => ⟨c, .refl, hx⟩
  | head hstep _ ih =>
    intro c hx
    obtain ⟨c₁, hst, hy⟩ := step_ofCoreK (hx ▸ hstep) K c rfl (noFX_store _)
    obtain ⟨c₂, hrun₂, hd⟩ := ih c₁ hy
    exact ⟨c₂, .head ((blockFX_noHost _) ▸ hst) hrun₂, hd⟩

/-- An infinite trace of Core code with live continuations starts with a Core step. -/
theorem step_of_traceK {K : List (Option ContFX)} {c : Config H}
    (h : Silmaril.InfiniteTrace (StepFX P noHost noFX) (ofCoreK K c)) :
    ∃ c', Step P noHost c c' ∧ Silmaril.InfiniteTrace (StepFX P noHost noFX) (ofCoreK K c') := by
  obtain ⟨y, hy, htr⟩ := h.unfold
  obtain ⟨c', hst, rfl⟩ := step_ofCoreK hy K c rfl (noFX_store _)
  exact ⟨c', (blockFX_noHost _) ▸ hst, htr⟩

/-- **Finite runs of `underHW` are Core runs of `withVals`.** -/
theorem runs_underHW {K : List (Option ContFX)} {hs : List HClause} {W : List Val}
    {d : ConfigFX H} {r : Result} (hd : d.code = r.toAdmin.map .core) {x : ConfigFX H}
    (hrun : StepsFX P noHost noFX x d) :
    ∀ c, x = underHW K hs W c → ∃ c', Steps P noHost (withVals W c) c' ∧ c'.code = r.toAdmin := by
  induction hrun using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun c hx => absurd (hx ▸ hd) (underHW_not_result r)
  | head hstep hrest ih =>
    intro c hx
    rcases step_underHW (hx ▸ hstep) with ⟨c', hst, rfl⟩ | ⟨r₀, -, rfl⟩ | ⟨vs, X, hX, rfl⟩
    · obtain ⟨c'', hrun', hc''⟩ := ih c' rfl
      exact ⟨c'', .head (lift_vals W hst) hrun', hc''⟩
    · obtain ⟨c'', hrun', rfl⟩ := runs_ofCoreK hrest _ rfl
      exact ⟨c'', hrun', map_core_inj hd⟩
    · rcases Relation.ReflTransGen.cases_head hrest with rfl | ⟨z, hz, -⟩
      · exact absurd (map_core_inj hd) (escape_not_result hX r)
      · exact absurd hz (escape_stuck hX)

/-- The invariant of `diverges_underHW`. -/
def DivInv (K : List (Option ContFX)) (hs : List HClause) (W : List Val) (c₀ : Config H) :
    Prop :=
  Silmaril.InfiniteTrace (StepFX P noHost noFX) (ofCoreK K c₀) ∨
    ∃ c, c₀ = withVals W c ∧ Silmaril.InfiniteTrace (StepFX P noHost noFX) (underHW K hs W c)

/-- `DivInv` is productive. -/
theorem divInv_step {K : List (Option ContFX)} {hs : List HClause} {W : List Val}
    {c₀ : Config H} (h : DivInv (P := P) K hs W c₀) :
    ∃ c₁, Step P noHost c₀ c₁ ∧ DivInv (P := P) K hs W c₁ := by
  rcases h with htr | ⟨c, rfl, htr⟩
  · obtain ⟨c₁, hst, htr₁⟩ := step_of_traceK htr
    exact ⟨c₁, hst, Or.inl htr₁⟩
  · obtain ⟨y, hy, htr'⟩ := htr.unfold
    rcases step_underHW hy with ⟨c', hst, rfl⟩ | ⟨r, -, rfl⟩ | ⟨vs, X, hX, rfl⟩
    · exact ⟨withVals W c', lift_vals W hst, Or.inr ⟨c', rfl, htr'⟩⟩
    · obtain ⟨c₁, hst, htr₁⟩ := step_of_traceK htr'
      exact ⟨c₁, hst, Or.inl htr₁⟩
    · obtain ⟨z, hz, -⟩ := htr'.unfold
      exact absurd hz (escape_stuck hX)

/-- **Divergence of `underHW` is Core divergence of `withVals`.** -/
theorem diverges_underHW {K : List (Option ContFX)} {hs : List HClause} {W : List Val}
    {c : Config H} (h : Silmaril.InfiniteTrace (StepFX P noHost noFX) (underHW K hs W c)) :
    Diverges P noHost (withVals W c) :=
  Silmaril.InfiniteTrace.coinduct (DivInv (P := P) K hs W) (fun _ hc => divInv_step hc)
    (Or.inr ⟨c, rfl, h⟩)

/-- **The CoreFX behaviours of `underHW K hs W c` are Core behaviours of `vals W ++ c`.** -/
theorem behaviours_underHW (K : List (Option ContFX)) (hs : List HClause) (W : List Val)
    (c : Config H) :
    behavioursFX P noHost noFX (underHW K hs W c) ⊆ behavioursOf P noHost (withVals W c) := by
  rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · obtain ⟨c', hc, hcode⟩ := runs_underHW hd hrun c rfl
    exact Or.inl ⟨c', r, hc, hcode, rfl⟩
  · exact Or.inr ⟨rfl, diverges_underHW hdiv⟩

end Silmaril.Proofs.Wasm.Models.FXLower
