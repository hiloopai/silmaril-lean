module

public import Silmaril.Proofs.Wasm.Dataflow.Fragment.Step

/-!
# The Wasm fragment of the dataflow DCE: theorems

The proofs are in `Silmaril.Proofs.Wasm.Dataflow.Fragment.Step`:

* `Step.noHost_of_frag`: a step of fragment code is a step without host;
* `Step.frag`: every configuration reachable from fragment code is fragment code;
* `pureArity_step_vals`, `pureArity_step`: a removable producer, applied to its
  operands, steps only to a single value, with store and frame unchanged (for every
  numerical profile and host);
* `codeSize_pos`: the stutter measure of nonempty code is positive.
-/
