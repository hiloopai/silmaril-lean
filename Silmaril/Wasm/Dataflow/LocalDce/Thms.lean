module

public import Silmaril.Proofs.Wasm.Dataflow.LocalDce.Sim

/-!
# an earlier step of the two-pass DCE, dead stores of locals: theorems

The proofs are in `Silmaril.Proofs.Wasm.Dataflow.LocalDce.{Basic,Clean,Sim}`:

* `localDceAdminSeq_append`, `localDceAdminSeq_expression`: the transform is a homomorphism
  for `++` and agrees with the source transform on source code;
* `localDce_step_sim`, `localDceSim`: the slide-68 simulation of *Optimising Compilers*
  (Lecture 5) on the Core 3.0 reduction relation, a stuttering forward simulation for every
  numerical profile and host. Only safety of the liveness solution is used
  (`liveSeq_loop_safe`), not that it is least;
* `localDce_result`, `localDce_returning`, `localDce_diverges`: a fragment function body,
  run under its outer label, and its pass-1 image reach the same result and store (or both
  return the same values, or both diverge), from any frames that agree on the body's
  live-in locals.
-/
