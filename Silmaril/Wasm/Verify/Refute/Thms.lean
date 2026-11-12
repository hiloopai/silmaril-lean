module

public import Silmaril.Wasm.Verify.Refute.Defs
public import Silmaril.Proofs.Wasm.Verify.Refute.Basic

@[expose] public section

/-!
# Counterexamples to import-call properties: results

Proofs in `Silmaril.Proofs.Wasm.Verify.Refute.Basic`. A counterexample `x` found by
`refuteStore I.store I.addrs imp i bad` on the store of an instance `I` (`IsInstance m mt I`,
`imp` the scalar type of import `i`):

* `candArgs_typed`: the candidate arguments are typed by the export's parameter types;
* `calloutOf?_sound`: a callout found by the interpreter is reached by a host-free Core run
  (silmaril-lean's `runInvoke?_steps_noHost`);
* **`refute_play`**: `[call j args, icall i x.callArgs]` is a play of `I.strategy P I.store`, for
  every profile `P` admitting the deterministic steps of `profile refOracle` (silmaril-lean's
  `ask_call_iff` agreement); **`refute_trace`**: it is a trace of `wasmSem P`;
* **`refute_closed_world`**: against every environment `K`, the Core run of the export call
  (`Steps P (hostOf I.imports K)`) reaches the callout of `i` with `x.callArgs`.

The run reaches the callout before any other import call, so no environment answer is used.
-/
