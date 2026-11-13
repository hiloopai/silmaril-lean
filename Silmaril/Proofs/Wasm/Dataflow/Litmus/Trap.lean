module

public import Silmaril.Wasm.Dataflow.Litmus.Defs
public import Silmaril.Wasm.Dataflow.Fused.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Stuck

/-!
# Litmus: the fused DCE simulation fails after a trap

`Trap.not_step_sim`: the step simulation of the fused transform is false for `Rel`.
`Trap.source_step`: the counterexample is reachable from fragment source code.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow.Litmus.Trap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

theorem dce_codeA : dceAdminSeq [] ⊥ codeA = [.trap] := by rfl

theorem dce_codeB : dceAdminSeq [] ⊥ codeB = codeB := by rfl

theorem frag_source : fragSeq source = true := by rfl

/-- `unreachable; i32.const 1; drop` steps to `codeA`. -/
theorem source_step (s : Store H) (f : Frame) :
    Step prof noHost ⟨s, f, expression source⟩ ⟨s, f, codeA⟩ :=
  .ctxtInstrs (vs := []) (rest := [one, .plain .drop]) (.parametric .unreachable)
    (.inr (List.cons_ne_nil _ _))

/-- The source step `codeA ↪ codeB`. -/
theorem stepAB (s : Store H) (f : Frame) : Step prof noHost ⟨s, f, codeA⟩ ⟨s, f, codeB⟩ := by
  have h1 : Step prof noHost ⟨s, f, vals [] ++ [Admin.trap] ++ [one]⟩ ⟨s, f, [.trap]⟩ :=
    .trapInstrs (.inr (List.cons_ne_nil _ _))
  exact .ctxtInstrs (vs := []) (rest := [.plain .drop]) h1 (.inr (List.cons_ne_nil _ _))

/-- **Counterexample.** From any store and frame, `codeA` steps to `codeB`, the target
`TRAP` is `Rel`-related to `codeA`, and no target configuration matches the step. -/
theorem counterexample (s : Store H) (f : Frame) :
    Step prof noHost ⟨s, f, codeA⟩ ⟨s, f, codeB⟩ ∧
    Rel [] ⊥ (⟨s, f, codeA⟩ : Config H) ⟨s, f, [.trap]⟩ ∧
    ¬ ∃ d₂, Rel [] ⊥ (⟨s, f, codeB⟩ : Config H) d₂ ∧
      (Relation.TransGen (Step prof noHost) ⟨s, f, [.trap]⟩ d₂ ∨
        (d₂ = ⟨s, f, [.trap]⟩ ∧ codeSize codeB < codeSize codeA)) := by
  refine ⟨stepAB s f, ⟨rfl, FrameRel.refl _ _, rfl, rfl, dce_codeA.symm⟩, ?_⟩
  rintro ⟨d₂, hr, hm⟩
  rcases hm with ht | ⟨rfl, -⟩
  · obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.mp ht
    exact not_step_trap hc
  · have hc : ([.trap] : List Admin) = codeB := hr.code.trans dce_codeB
    simp [codeB] at hc

/-- The fused step simulation is false for `Rel`: it fails on `codeA`. -/
theorem not_step_sim (s : Store H) (f : Frame) :
    ¬ ∀ c₁ c₂ d₁ : Config H, Step prof noHost c₁ c₂ → Rel [] ⊥ c₁ d₁ →
      ∃ d₂, Rel [] ⊥ c₂ d₂ ∧
        (Relation.TransGen (Step prof noHost) d₁ d₂ ∨
          (d₂ = d₁ ∧ codeSize c₂.code < codeSize c₁.code)) := fun hall =>
  (counterexample s f).2.2 (hall _ _ _ (counterexample s f).1 (counterexample s f).2.1)

end Silmaril.Wasm.Dataflow.Litmus.Trap
