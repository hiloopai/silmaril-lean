module

public import Silmaril.Proofs.Wasm.Models.FXTRunX.Sound

/-!
# The `StepFXT` interpreter with traps is sound

Statements and proofs in `Silmaril.Proofs.Wasm.Models.FXTRunX`:

* **`xstep_sound`**: every trap step (`resume` of a consumed continuation; a trap after values
  or before code; a label, frame or handler around a trap) is a `StepFXT` step;
* **`stepX_sound`**, **`runX_sound`**: the combined step function (a `tstep` step, else a trap
  step) and its runs are `StepFXT` steps and runs;
* **`checkTrapX_mem`**: if `checkTrapX` holds (the computed run ends with the code `trap` and
  the log `log`), then `ObsT.ret log traps` is a `StepFXT` behaviour.

Membership only, as for `checkT_mem`.

A Silmaril addition (Follow-up 5 workflow, track fx).
-/
