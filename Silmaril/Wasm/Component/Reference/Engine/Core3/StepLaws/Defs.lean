module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Extends.Defs
public import Silmaril.Wasm.Component.Engine.Core3.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.StepLaws.Grows.Defs
import Silmaril.Wasm.Component.Reference.Engine.Core3.StepLaws.Callout.Defs
import Silmaril.Wasm.Component.Reference.Engine.Core3.StepLaws.Terminal.Defs

/-!
# Parked threads of the concrete Core 3.0 engine take no step

The status of `core3 o` is the flat view of `SingleThreaded.statusC (stepI o)`
(`statusE_eq_flatStatus`). Every status other than `running` means that the interpreter has
no step at the thread's configuration (`stepI_none_of_statusC_ne_running`), without any typing:
`returned` codes are values, a lone `trap` or an uncaught exception
(StepLaws/Terminal.lean), a `callout` is a host-call redex (StepLaws/Callout.lean), and
`stuck` means `stepI` is `none` by definition. Hence the internal step of `core3 o` is `none`
on every non-`running` thread (`statusE_not_running_no_step`), which gives the
`returned_no_step`, `callout_no_step` and `stuck_no_step` laws of `CoreEngine.Lawful`
(`statusE_returned_no_step`, `statusE_callout_no_step`, `statusE_stuck_no_step`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core

variable {H : Type}

theorem stepI_none_of_statusC_ne_running {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread}
    (h : SingleThreaded.statusC (SingleThreaded.Exec.stepI o) s t ≠ .running) :
    SingleThreaded.Exec.stepI o (t.config s) = none := by
  by_cases h1 : (SingleThreaded.splitVals (t.config s).code).2.isEmpty = true
  · exact stepI_of_splitVals_isEmpty h1
  by_cases h2 : SingleThreaded.isTrap? (t.config s).code = true
  · exact stepI_trap ((SingleThreaded.isTrap?_iff _).mp h2)
  by_cases h3 : SingleThreaded.isThrowing? (t.config s).code = true
  · obtain ⟨a, e⟩ := (SingleThreaded.isThrowing?_iff _).mp h3
    exact stepI_throwing e
  rw [statusC_of_live h1 h2 h3] at h
  cases hd : SingleThreaded.decompose? s (t.config s).code with
  | some x =>
    apply stepI_none_of_decompose? (x := x)
    rwa [SingleThreaded.Thread.config_store]
  | none =>
    cases hc : SingleThreaded.Exec.stepI o (t.config s) with
    | none => rfl
    | some c' => simp [hd, hc] at h

/-- A thread that is not `running` takes no internal step of the concrete engine. -/
theorem statusE_not_running_no_step {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} (h : statusE o s t ≠ .running) :
    SingleThreaded.internalC (SingleThreaded.Exec.stepI o) (s, t) = none := by
  rw [statusE_eq_flatStatus] at h
  have h' := stepI_none_of_statusC_ne_running fun e => h (flatStatus_running_iff.mpr e)
  show Option.map _ (SingleThreaded.Exec.stepI o (t.config s)) = none
  rw [h']
  rfl

theorem statusE_returned_no_step {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} {r : CallResult} {c' : Store H × SingleThreaded.Thread}
    (h : statusE o s t = .returned r) :
    ¬ SingleThreaded.internalC (SingleThreaded.Exec.stepI o) (s, t) = some c' := by
  rw [statusE_not_running_no_step (by rw [h]; intro e; cases e)]
  exact fun e => nomatch e

theorem statusE_callout_no_step {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} {hc : H} {args : List FlatValue}
    {c' : Store H × SingleThreaded.Thread} (h : statusE o s t = .callout hc args) :
    ¬ SingleThreaded.internalC (SingleThreaded.Exec.stepI o) (s, t) = some c' := by
  rw [statusE_not_running_no_step (by rw [h]; intro e; cases e)]
  exact fun e => nomatch e

theorem statusE_stuck_no_step {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} {c' : Store H × SingleThreaded.Thread}
    (h : statusE o s t = .stuck) :
    ¬ SingleThreaded.internalC (SingleThreaded.Exec.stepI o) (s, t) = some c' := by
  rw [statusE_not_running_no_step (by rw [h]; intro e; cases e)]
  exact fun e => nomatch e

end Silmaril.Wasm.Component.Engine.Core3
