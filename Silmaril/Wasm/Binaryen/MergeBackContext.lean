module

public import Silmaril.Wasm.Binaryen.MergeBackMatching

@[expose] public section

/-! # Administrative contexts for matching backward merge steps

These combinators lift a backward step that retains `Simulation.Matching`
through every administrative context constructor. They preserve the particular
target successor, rather than obtaining an unrelated source progress witness.
-/

namespace Silmaril.Wasm.Binaryen.MergeUntyped

open Execution.Core Numerics
open Silmaril.Wasm.Link.GC Silmaril.Wasm.Link.GC.AdminRelation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The given target transition can be reproduced from every related, scoped
source, preserving the relation to that exact target successor. -/
def BackwardStep (P : Profile) (host : HostSemantics H) (target target' : Config H) : Prop :=
  ∀ {mode : Mode} {source : Config H}, Simulation.Matching mode source target →
    XAs source.frame.module source.code →
    ∃ source', Step P host source source' ∧ Simulation.Matching mode source' target'

namespace BackwardStep

theorem parametric {s : Store H} {f : Frame} {code out : List Admin}
    (step : ParametricStep code out) : BackwardStep P host ⟨s, f, code⟩ ⟨s, f, out⟩ := by
  intro mode source matching _
  exact ⟨_, parametric_back_matching step matching⟩

theorem numeric {s : Store H} {f : Frame} {code out : List Admin}
    (step : NumericStep P code out) : BackwardStep P host ⟨s, f, code⟩ ⟨s, f, out⟩ := by
  intro mode source matching _
  exact ⟨_, numeric_back_matching step matching⟩

theorem vector {s : Store H} {f : Frame} {code out : List Admin}
    (step : VectorStep P code out) : BackwardStep P host ⟨s, f, code⟩ ⟨s, f, out⟩ := by
  intro mode source matching _
  exact ⟨_, vector_back_matching step matching⟩

/-- Matching backward steps lift through operand prefixes and instruction suffixes. -/
theorem instrs {s s' : Store H} {f f' : Frame} {vs : List Val}
    {code out rest : List Admin} (step : Step P host ⟨s, f, code⟩ ⟨s', f', out⟩)
    (nonempty : vs ≠ [] ∨ rest ≠ [])
    (inner : BackwardStep P host ⟨s, f, code⟩ ⟨s', f', out⟩) :
    BackwardStep P host ⟨s, f, vals vs ++ code ++ rest⟩
      ⟨s', f', vals vs ++ out ++ rest⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching scope
  have control := matching.code
  rw [List.append_assoc] at control
  obtain ⟨R, rfl, hR⟩ := control.vals_right
  obtain ⟨A, B, rfl, hA, hB⟩ := hR.append_right
  simp only [xas_append_iff] at scope
  obtain ⟨⟨s₁, f₁, A'⟩, sourceStep, paired⟩ :=
    inner (source := ⟨s₀, f₀, A⟩) ⟨matching.stores, matching.frames, hA⟩ scope.2.1
  have nonempty' : vs ≠ [] ∨ B ≠ [] := by
    rcases nonempty with h | h
    · exact .inl h
    · right
      intro hb
      subst hb
      exact h hB.nil_left
  refine ⟨⟨s₁, f₁, vals vs ++ A' ++ B⟩, ?_, paired.stores, paired.frames, ?_⟩
  · simpa only [List.append_assoc] using Step.ctxtInstrs sourceStep nonempty'
  · have suffix : Control mode f₁.module f'.module B rest := by
      rw [sourceStep.frame_module, step.frame_module]
      exact hB
    exact ((Control.values _ _ _ vs).append paired.code).append suffix

/-- Matching backward steps lift through labels, keeping the continuation relation. -/
theorem label {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {code out : List Admin}
    (inner : BackwardStep P host ⟨s, f, code⟩ ⟨s', f', out⟩) :
    BackwardStep P host ⟨s, f, [.label n cont code]⟩ ⟨s', f', [.label n cont out]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching scope
  obtain ⟨cont₀, body₀, rest, rfl, hcont, hb, hr⟩ := matching.code.label_right
  obtain rfl := hr.nil_right
  simp only [xas_cons_iff, xa_label, xas_nil, and_true] at scope
  obtain ⟨⟨s₁, f₁, body₁⟩, sourceStep, paired⟩ :=
    inner (source := ⟨s₀, f₀, body₀⟩) ⟨matching.stores, matching.frames, hb⟩ scope.2
  exact ⟨⟨s₁, f₁, [.label n cont₀ body₁]⟩, .ctxtLabel sourceStep,
    paired.stores, paired.frames, .label hcont paired.code .nil⟩

/-- A nested call frame selects its own mode in the backward relation. -/
theorem frame {s s' : Store H} {caller f f' : Frame} {n : Nat}
    {code out : List Admin}
    (inner : BackwardStep P host ⟨s, f, code⟩ ⟨s', f', out⟩) :
    BackwardStep P host ⟨s, caller, [.frame n f code]⟩
      ⟨s', caller, [.frame n f' out]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching scope
  obtain ⟨innerMode, fi₀, body₀, rest, rfl, hfi, hb, hr⟩ := matching.code.frame_right
  obtain rfl := hr.nil_right
  simp only [xas_cons_iff, xa_frame, xas_nil, and_true] at scope
  obtain ⟨⟨s₁, f₁, body₁⟩, sourceStep, paired⟩ :=
    inner (source := ⟨s₀, fi₀, body₀⟩) ⟨matching.stores, hfi, hb⟩ scope
  exact ⟨⟨s₁, f₀, [.frame n f₁ body₁]⟩, .ctxtFrame sourceStep,
    paired.stores, matching.frames, .frame paired.frames paired.code .nil⟩

/-- Handler contexts remain in the unchanged mode on both sides. -/
theorem handler {s s' : Store H} {f f' : Frame} {n : Nat} {catches : List Catch}
    {code out : List Admin} (step : Step P host ⟨s, f, code⟩ ⟨s', f', out⟩)
    (inner : BackwardStep P host ⟨s, f, code⟩ ⟨s', f', out⟩) :
    BackwardStep P host ⟨s, f, [.handler n catches code]⟩
      ⟨s', f', [.handler n catches out]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching scope
  obtain ⟨body₀, rest, rfl, rfl, modules, hb, hr⟩ := matching.code.handler_right
  obtain rfl := hr.nil_right
  simp only [xas_cons_iff, xa_handler, xas_nil, and_true] at scope
  obtain ⟨⟨s₁, f₁, body₁⟩, sourceStep, paired⟩ :=
    inner (source := ⟨s₀, f₀, body₀⟩) ⟨matching.stores, matching.frames, hb⟩ scope
  have modules' : f₁.module = f'.module := by
    rw [sourceStep.frame_module, step.frame_module]
    exact modules
  refine ⟨⟨s₁, f₁, [.handler n catches body₁]⟩, .ctxtHandler sourceStep,
    paired.stores, paired.frames, ?_⟩
  have output := paired.code
  change Control .same f₁.module f'.module _ _ at output ⊢
  rw [← modules'] at output ⊢
  exact .handler output .nil

end BackwardStep

end Silmaril.Wasm.Binaryen.MergeUntyped
