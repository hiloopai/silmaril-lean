module

public import Silmaril.Proofs.Wasm.Dataflow.DropElim.Sim

/-!
# an earlier step of the two-pass DCE, dropped pure producers: theorems

The proofs are in `Silmaril.Proofs.Wasm.Dataflow.DropElim.{Erase,Match,Struct,Pure,Sim}`:

* `dropElim_erase`: the pass is an erasure;
* `erase_step_sim`, `eraseSim`: erasure is a stuttering forward simulation that keeps the
  store and the frame *equal*, for every numerical profile and host;
* `dropElim_result`, `dropElim_returning`, `dropElim_diverges`: a function body (any body,
  not only fragment code) and its pass-2 image reach the same result, store and frame, or
  both return the same values, or both diverge.
-/
