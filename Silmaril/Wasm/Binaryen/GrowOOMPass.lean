module

public import Silmaril.Wasm.Binaryen.GrowOOMMode

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowOOM

open Execution.Core Numerics Validation Optimization

variable {H : Type}

/-- The real full-module candidate is certified only for trap insertion. Its
runtime fallback remains identity outside the exact accepted zero-delta family. -/
def trapInsertionP (P : Profile) :
    Silmaril.Compile.PassAPI.Pass (Modes.contract .trapInsertion P (closedHost (H := H))) where
  run := optimize
  inv_run {m} hm := by
    unfold optimize
    split
    · change (BModule.lift (mod _)).Ok
      exact ⟨_, by rw [lower_lift]; exact module_ok _⟩
    · exact hm
  sound {m} _ := by
    change Modes.ExportCorrect .trapInsertion P closedHost m.lower (optimize m).lower
    unfold optimize
    split
    · rename_i a accepted
      rw [lower_lift, recognize?_sound accepted]
      exact exportCorrect a
    · exact Modes.ExportCorrect.refl _ _ _ _

/-- A first failed growth produces a target trap with the real invocation run. -/
theorem failure_observation (a : AddrType) :
    [.returns [], .traps] ∈ moduleObs (Profile.spec true {}) (closedHost (H := H))
      {} [] (mod a) [("grow", [])] := by
  apply (moduleObs_iff (P := Profile.spec true {}) {} a [] [("grow", [])] _).mpr
  refine ⟨rfl, [.traps], ?_, rfl⟩
  exact .done (r := .trap)
    ((GrowWrapper.exportFunc_iff ({} : Store H) a "grow" 0).mpr ⟨rfl, rfl⟩)
    ((call_invokeOk_iff {} a true []).mpr rfl)
    (call_run (P := Profile.spec true {}) {} a true true (by trivial)) rfl .nil

/-- The same source wrapper cannot trap on that call: the real run inversion
admits only successful size returns and the failure sentinel. -/
theorem source_not_trap (a : AddrType) (P : Profile) :
    [.returns [], .traps] ∉ moduleObs P (closedHost (H := H))
      {} [] (GrowWrapper.mod a 0 false) [("grow", [])] := by
  intro hs
  obtain ⟨_, tail, hsession, he⟩ :=
    (GrowWrapper.moduleObs_iff (P := P) ({} : Store H) a 0 false [] [("grow", [])] _).mp hs
  have htail : tail = [.traps] := (List.cons.inj he).2.symm
  cases hsession with
  | stop _ => cases htail
  | @done _ _ _ _ address c result bs ha hok run hr tail =>
    obtain ⟨_, rfl⟩ := (GrowWrapper.exportFunc_iff ({} : Store H) a "grow" address).mp ha
    obtain ⟨failure, _, _, rfl⟩ := call_run_inv (P := P) {} a false run hr
    cases failure <;> simp [callResult, Result.toBehaviour] at htail
  | diverge => cases htail

/-- This is strictly insertion-only, rather than a renamed refinement pass. -/
theorem not_refinement (a : AddrType) :
    ¬ Modes.ExportCorrect .refinement (Profile.spec true {}) (closedHost (H := H))
      (GrowWrapper.mod a 0 false) (mod a) := by
  intro correct
  have allowed := (correct.observations {} [] [("grow", [])] LoopCex.storeOk_empty).1
    (failure_observation (H := H) a)
  exact source_not_trap (H := H) a _ allowed

end Silmaril.Wasm.Binaryen.GrowOOM
