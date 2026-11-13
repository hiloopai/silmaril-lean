module

public import Silmaril.Wasm.FX.Examples.Control.Defs
public import Silmaril.Wasm.Models.FXL.Thms

/-!
# `control0`/`prompt0` programs: their only behaviours

Each run is a closed evaluation of `runN` (checked by the kernel, `decide +kernel`); by
determinism of `StepFXL` (`FXL.beh_eq_of_out`) its outcome is the program's **only** behaviour:

* **`abort_beh`**: `h` drops the continuation: log `1 2 4`;
* **`resume_beh`**: `h` resumes it once: log `1 2 3 4 5`;
* **`escape_beh`**: the continuation does not include the prompt, so a `control0` in a
  continuation resumed without a handler reaches the outer prompt: log `1 2 3 5 9 10`;
* **`outside_beh`**: `h` runs outside its prompt: log `1 2 3 4 5`;
* **`twice_beh`**: a second `resume` of the continuation traps after log `1 2`.

All programs return no values.

A Silmaril addition (Follow-up 5 workflow, track fx).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples.Control

open Silmaril.Wasm.Models.FXL

theorem abort_run : (runN abortP ctlAr 200 (init abortP 5)).out = some (.done abortLog []) := by
  decide +kernel

/-- **Abort**: the only behaviour prints `1 2 4`. -/
theorem abort_beh : beh abortP ctlAr (init abortP 5) = {.done abortLog []} :=
  beh_eq_of_out abort_run

theorem resume_run : (runN resumeP ctlAr 200 (init resumeP 5)).out =
    some (.done resumeLog []) := by
  decide +kernel

/-- **Resume once**: the only behaviour prints `1 2 3 4 5`. -/
theorem resume_beh : beh resumeP ctlAr (init resumeP 5) = {.done resumeLog []} :=
  beh_eq_of_out resume_run

theorem escape_run : (runN escapeP ctlAr 400 (init escapeP 6)).out =
    some (.done escapeLog []) := by
  decide +kernel

/-- **The continuation excludes the prompt**: the only behaviour prints `1 2 3 5 9 10`. -/
theorem escape_beh : beh escapeP ctlAr (init escapeP 6) = {.done escapeLog []} :=
  beh_eq_of_out escape_run

theorem outside_run : (runN outsideP ctlAr 400 (init outsideP 6)).out =
    some (.done outsideLog []) := by
  decide +kernel

/-- **The handler runs outside the prompt**: the only behaviour prints `1 2 3 4 5`. -/
theorem outside_beh : beh outsideP ctlAr (init outsideP 6) = {.done outsideLog []} :=
  beh_eq_of_out outside_run

theorem twice_run : (runN twiceP ctlAr 200 (init twiceP 5)).out = some (.trap twiceLog) := by
  decide +kernel

/-- **One-shot**: the only behaviour traps after printing `1 2`. -/
theorem twice_beh : beh twiceP ctlAr (init twiceP 5) = {.trap twiceLog} :=
  beh_eq_of_out twice_run

end Silmaril.Wasm.FX.Examples.Control
