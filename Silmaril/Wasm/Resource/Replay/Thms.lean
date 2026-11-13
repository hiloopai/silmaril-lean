module

public import Silmaril.Wasm.Resource.Replay.Defs
public import Silmaril.Proofs.Wasm.Resource.Replay.Basic

@[expose] public section

/-!
# Replaying environment answers on real modules: results

Proofs in `Silmaril.Proofs.Wasm.Resource.Replay.Basic`. For an instance `I` with `I.Ok`, every
profile `P` admitting the deterministic steps of `profile refOracle`:

* `reach_of_steps'`: a host-free Core run from a thread's configuration is a machine run;
  `fill_typed`: plugging values typed by the callee's result types into a typed callout context
  gives a typed configuration (silmaril-lean's `Ctx.fill_callout_typed`).
* **`replayFrom_path`**: the moves recorded by `replayFrom` from a typed running state are read
  off a path of `I`'s transition system (`rmv` reads a move with plain indices);
  **`replayExport_play`**, `replayRefute_play`: a replay of an export call is a play of
  `I.strategy P I.store`.
* **`not_models_of_replay`**: a replay rejected by a protocol `pr` refutes `pr.comap c` in
  `protoLogic` over `wasmSem P`, for a classifier `c` factoring through `RMove.ofEvent`
  (`clientEv_eq`, `obEv_eq`).
* **`client_refuted_replay_inst`**, **`ob_refuted_replay_inst`** (instances, every such profile);
  **`client_refuted_replay`**, **`ob_refuted_replay`** (modules, every specification profile
  `Profile.spec nd {}`).

Tactics: `resource_refute_replay` closes `¬ Models (protoLogic …) (wasmSem (Profile.spec nd {}))
(progOf m) (clientSpec ia iu if_)` by `client_refuted_replay` (up to `8` callouts) and kernel
evaluation; `resource_refute_ob` closes the same for `obSpec r.toOB` by `ob_refuted_replay`.
-/

namespace Silmaril.Wasm.Resource

/-- Refute the client sentence on a module by replaying environment answers. -/
macro "resource_refute_replay" : tactic =>
  `(tactic| (apply client_refuted_replay (n := 8) <;> decide +kernel))

/-- Refute the ownership sentence `obSpec r.toOB` on a module by replaying environment answers. -/
macro "resource_refute_ob" : tactic =>
  `(tactic| (apply ob_refuted_replay (n := 8) <;> decide +kernel))

end Silmaril.Wasm.Resource
