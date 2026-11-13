module

public import Silmaril.Wasm.Resource.Check.Defs
public import Silmaril.Proofs.Wasm.Resource.Check.Basic

@[expose] public section

/-!
# Checking handle protocols on modules: results

Proofs in `Silmaril.Proofs.Wasm.Resource.Check.Basic`.

* `client_first_rejected`: a first event `use h` or `free h` is rejected by the client sentence.
* **`client_refuted_inst`**, **`client_refuted`**: a `firstCall?` counterexample (an export call
  whose first import call is `use` or `free`, found by the verified interpreter) refutes the
  client sentence, at every profile admitting the refuter's deterministic steps, resp. every
  specification profile `Profile.spec nd {}`.
* **`clientSpec_check`**: `proved` verdicts of `Silmaril.Wasm.Verify.check` for "never calls `use`"
  and "never calls `free`" give the client sentence, every profile.

Tactics: `resource_refute` closes `¬ Models (protoLogic …) (wasmSem (Profile.spec nd {}))
(progOf m) (clientSpec ia iu if_)` by `client_refuted` and kernel evaluation;
`resource_check` closes `Models (protoLogic …) (wasmSem P) (progOf m) (clientSpec ia iu if_)` by
`clientSpec_check` and kernel evaluation.
-/

namespace Silmaril.Wasm.Resource

/-- Refute the client sentence on a module through the first-call refuter (use, then free). -/
macro "resource_refute" : tactic => `(tactic| first
  | (apply client_refuted (hk := .inl rfl) <;> decide +kernel)
  | (apply client_refuted (hk := .inr rfl) <;> decide +kernel))

/-- Prove the client sentence on a module that never calls `use` and `free`, by the verifier. -/
macro "resource_check" : tactic => `(tactic| (apply clientSpec_check <;> decide +kernel))

end Silmaril.Wasm.Resource
