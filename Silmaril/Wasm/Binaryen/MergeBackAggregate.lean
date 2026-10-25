module

public import Silmaril.Wasm.Binaryen.MergeBackState

@[expose] public section

/-! # Exact backward aggregate matching for module merging

The existing source-progress proof can retain its actual AggregateStep witness.
Forward aggregate simulation then produces an aggregate successor of the same
target redex. AggregateStep.det identifies that successor with the chosen target
result. This local family theorem has no numerical-profile parameter: it does
not assume numerical determinism or choose another profile-dependent outcome.
-/

namespace Silmaril.Wasm.Binaryen.MergeUntyped

open Execution.Core Numerics SingleThreaded.Det
open Silmaril.Wasm.Link.GC Silmaril.Wasm.Link.GC.AdminRelation

variable {H : Type}

private theorem aggregate_forward_matching {mode : Mode}
    {source source' target : Config H} (step : AggregateStep source source')
    (matching : Simulation.Matching mode source target) :
    ∃ target', AggregateStep target target' ∧ Simulation.Matching mode source' target' := by
  rcases source' with ⟨store', frame', out⟩
  have framesEqual : frame' = source.frame := by cases step <;> rfl
  subst frame'
  obtain ⟨resultStore, resultCode, actual, stores, code⟩ :=
    AggregateSimulation.aggregate matching.stores matching.frames.view step matching.code
  exact ⟨⟨resultStore, target.frame, resultCode⟩, actual,
    ⟨stores, matching.frames, code⟩⟩

/-- Allocation, field access, mutation and array copy/fill unrolling match the
actual chosen target result, including unchanged ambient segment instructions.
Source annotation scope is retained; source typing is not required. -/
theorem aggregate_back_matching {P : Profile} {host : HostSemantics H} {mode : Mode}
    {source target target' : Config H} (step : AggregateStep target target')
    (matching : Simulation.Matching mode source target)
    (scope : XAs source.frame.module source.code) :
    ∃ source', Step P host source source' ∧ Simulation.Matching mode source' target' := by
  obtain ⟨source', actual⟩ := aggregate_back_progress step matching.stores
    matching.frames matching.code scope
  obtain ⟨result, targetStep, resultMatching⟩ := aggregate_forward_matching actual matching
  rcases target with ⟨s, f, code⟩
  have same : result = target' := (AggregateStep.det (p := []) targetStep step rfl).2
  exact ⟨source', .aggregate actual, same ▸ resultMatching⟩

theorem BackwardStep.aggregate {P : Profile} {host : HostSemantics H}
    {target target' : Config H} (step : AggregateStep target target') :
    BackwardStep P host target target' := by
  intro mode source matching scope
  exact aggregate_back_matching step matching scope

end Silmaril.Wasm.Binaryen.MergeUntyped
