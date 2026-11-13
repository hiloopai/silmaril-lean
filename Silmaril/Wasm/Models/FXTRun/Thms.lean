module

public import Silmaril.Proofs.Wasm.Models.FXTRun.Seg

/-!
# The `StepFXT` interpreter is sound

The step function `tstep` of `Silmaril.Wasm.Models.FXTRun` computes `StepFXT` steps
(statements and proofs in `Silmaril.Proofs.Wasm.Models.FXTRun`, namespace
`Silmaril.Proofs.Wasm.Models.FXTRun`):

* **`tstep_sound`**: every step it computes is a `StepFXT` step (store and frame unchanged),
  for every profile and host;
* **`runT_sound`**: a computed run `runT` is a `StepsT` run;
* **`checkT_mem`**: if `checkT` holds (the computed run ends with empty code and log `log`),
  then `ObsT.ret log (returns [])` is a `StepFXT` behaviour of the configuration;
* **`segT_steps`**: a checked segment (`segT`: the computed run agrees with a given
  configuration, `sameCfg`) is a `StepsT` run to it, and `mem_of_stepsT` prepends a run to a
  finished behaviour, so a long run can be checked in segments.

So a closed evaluation of `checkT` (by `decide +kernel`) proves that a program prints a given
log. It proves membership only: that this is the program's *only* `StepFXT` behaviour is not
proved (`StepFX'` is not deterministic in general, e.g. its untyped `suspend` may split the
payload anywhere).

A Silmaril addition.
-/
