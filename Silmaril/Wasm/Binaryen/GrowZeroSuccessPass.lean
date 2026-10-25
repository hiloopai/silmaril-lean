module

public import Silmaril.Wasm.Binaryen.GrowZeroSuccessMode
public import Silmaril.Wasm.Binaryen.PassAPI.ModePipeline

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowZeroSuccess

open Execution.Core Numerics Validation Optimization MemoryGrowFailure

variable {H : Type}

/-- Shared-API feasible refinement with an explicit success permission. -/
def refinementP_of_success (P : Profile) (success : ZeroGrowSuccess P) :
    Silmaril.Compile.PassAPI.Pass (Modes.contract .refinement P (closedHost (H := H))) where
  run := optimize
  inv_run {m} hm := by
    unfold optimize
    split
    · change (BModule.lift (mod _)).Ok
      exact ⟨_, by rw [lower_lift]; exact module_ok _⟩
    · exact hm
  sound {m} _ := by
    change Modes.ExportCorrect .refinement P closedHost m.lower (optimize m).lower
    unfold optimize
    split
    · rename_i a accepted
      rw [lower_lift, recognize?_sound accepted]
      exact exportCorrect_of_success success a
    · exact Modes.ExportCorrect.refl _ _ _ _

/-- The standard spec permits successful zero growth at both address widths,
independently of the numerical nondeterminism and relaxed-SIMD builtins. -/
def refinementP (nd : Bool := true) (r : RelaxedChoice := {}) :
    Silmaril.Compile.PassAPI.Pass
      (Modes.contract .refinement (Profile.spec nd r) (closedHost (H := H))) :=
  refinementP_of_success (Profile.spec nd r) (zeroGrowSuccess_spec nd r)

theorem optimize_sound (nd : Bool) (r : RelaxedChoice) {m : BModule} (hm : m.Ok) :
    (optimize m).Ok ∧
      Modes.ExportCorrect .refinement (Profile.spec nd r) (closedHost (H := H))
        m.lower (optimize m).lower :=
  ⟨(refinementP (H := H) nd r).inv_run hm, (refinementP (H := H) nd r).sound hm⟩

/-- Mode selection rejects this stage when exact equivalence is requested. -/
def stage (nd : Bool := true) (r : RelaxedChoice := {}) :
    Modes.Stage (Profile.spec nd r) (closedHost (H := H)) :=
  ⟨"select-zero-grow-success", .refinement, refinementP nd r⟩

/-- The eliminated source alternative is a genuine executed trap, not an
abstract choice or an empty behavior set. -/
theorem failure_observation (a : AddrType) (nd : Bool) (r : RelaxedChoice) :
    [.returns [], .traps] ∈ moduleObs (Profile.spec nd r) (closedHost (H := H))
      {} [] (GrowOOM.mod a) [("grow", [])] := by
  apply (GrowOOM.moduleObs_iff (P := Profile.spec nd r) {} a [] [("grow", [])] _).mpr
  refine ⟨rfl, [.traps], ?_, rfl⟩
  exact .done (r := .trap)
    ((GrowWrapper.exportFunc_iff ({} : Store H) a "grow" 0).mpr ⟨rfl, rfl⟩)
    ((GrowOOM.invokeOk_iff {} a []).mpr rfl)
    (GrowOOM.call_run (P := Profile.spec nd r) {} a true true (by trivial)) rfl .nil

/-- The real constant-return target cannot produce that trap at any profile. -/
theorem target_not_trap (a : AddrType) (P : Profile) :
    [.returns [], .traps] ∉ moduleObs P (closedHost (H := H))
      {} [] (mod a) [("grow", [])] := by
  intro hs
  obtain ⟨_, tail, hsession, he⟩ :=
    (moduleObs_iff (P := P) ({} : Store H) a [] [("grow", [])] _).mp hs
  have htail : tail = [.traps] := (List.cons.inj he).2.symm
  cases hsession with
  | stop _ => cases htail
  | @done _ _ _ _ address c result bs ha _ run hr _ =>
    obtain ⟨_, rfl⟩ := (GrowWrapper.exportFunc_iff ({} : Store H) a "grow" address).mp ha
    obtain ⟨_, rfl⟩ := target_run_inv (P := P) {} a run hr
    cases htail
  | diverge => cases htail

/-- Optional trap removal is strictly refinement, not exact equivalence. -/
theorem not_equivalence (a : AddrType) (nd : Bool) (r : RelaxedChoice) :
    ¬ Modes.ExportCorrect .equivalence (Profile.spec nd r) (closedHost (H := H))
      (GrowOOM.mod a) (mod a) := by
  intro correct
  have trap := failure_observation (H := H) a nd r
  rw [correct.observations {} [] [("grow", [])] LoopCex.storeOk_empty] at trap
  exact target_not_trap (H := H) a _ trap

/-- A concrete target observation witnesses nonvacuity for every profile. -/
theorem success_observation (a : AddrType) (P : Profile) :
    [.returns [], .returns [addrVal a 0]] ∈ moduleObs P (closedHost (H := H))
      {} [] (mod a) [("grow", [])] := by
  apply (moduleObs_iff (P := P) {} a [] [("grow", [])] _).mpr
  refine ⟨rfl, [.returns [addrVal a 0]], ?_, rfl⟩
  exact .done (r := .values [addrVal a 0])
    ((GrowWrapper.exportFunc_iff ({} : Store H) a "grow" 0).mpr ⟨rfl, rfl⟩)
    ((invokeOk_iff {} a []).mpr rfl) (target_forced {} a).steps rfl .nil

/-- The success premise cannot be dropped: if zero growth is forced to fail,
the guarded source cannot return the target's zero result. -/
theorem source_not_success_of_forced_failure (a : AddrType) (P : Profile)
    (noSuccess : ¬ P.growMaySucceed .memory 0 0 0) :
    [.returns [], .returns [addrVal a 0]] ∉
      moduleObs P (closedHost (H := H)) {} [] (GrowOOM.mod a) [("grow", [])] := by
  intro hs
  obtain ⟨_, tail, hsession, he⟩ :=
    (GrowOOM.moduleObs_iff (P := P) ({} : Store H) a [] [("grow", [])] _).mp hs
  have htail : tail = [.returns [addrVal a 0]] := (List.cons.inj he).2.symm
  cases hsession with
  | stop _ => cases htail
  | @done _ _ _ _ address c result bs ha _ run hr _ =>
    obtain ⟨_, rfl⟩ := (GrowWrapper.exportFunc_iff ({} : Store H) a "grow" address).mp ha
    obtain ⟨failure, allowed, _, rfl⟩ := GrowOOM.call_run_inv (P := P) {} a true run hr
    cases failure
    · exact noSuccess allowed
    · simp [GrowOOM.callResult, GrowOOM.guardResult, Result.toBehaviour] at htail
  | diverge => cases htail

theorem not_refinement_of_forced_failure (a : AddrType) (P : Profile)
    (noSuccess : ¬ P.growMaySucceed .memory 0 0 0) :
    ¬ Modes.ExportCorrect .refinement P (closedHost (H := H)) (GrowOOM.mod a) (mod a) := by
  intro correct
  exact source_not_success_of_forced_failure (H := H) a P noSuccess
    ((correct.observations {} [] [("grow", [])] LoopCex.storeOk_empty).1
      (success_observation (H := H) a P))

/-- A deterministic always-failing growth oracle supplies an explicit
counterexample to any profile-uniform version of this rewrite. -/
theorem not_refinement_fail_only (a : AddrType) :
    ¬ Modes.ExportCorrect .refinement (Profile.deterministic (fun _ _ _ _ => true))
      (closedHost (H := H)) (GrowOOM.mod a) (mod a) := by
  apply not_refinement_of_forced_failure
  simp [Profile.growMaySucceed, Profile.deterministic]

/-- A deterministic `unreachable` module is outside the exact growth shape;
its trap is preserved by identity fallback. -/
theorem deterministic_trap_fallback (a : AddrType) :
    optimize (BModule.lift { GrowOOM.mod a with
      funcs := [⟨⟨0⟩, [], [.unreachable]⟩] }) =
    BModule.lift { GrowOOM.mod a with funcs := [⟨⟨0⟩, [], [.unreachable]⟩] } := by
  apply optimize_of_rejected
  rw [lower_lift]
  cases a <;> with_unfolding_all rfl

end Silmaril.Wasm.Binaryen.GrowZeroSuccess
