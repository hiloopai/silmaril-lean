module

public import Silmaril.Wasm.Spec.Wasm.Defs
public import Silmaril.Proofs.Wasm.Spec.Wasm.Ground

@[expose] public section

/-!
# Wasm traces and Core 3.0 behaviours: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Wasm.Ground`. Every profile `P`.

* `call_ret_mem_iff`: **traces are Core runs**: `[call j a, ret j b]` is a trace of `p` iff a
  host-free Core run of `$invoke(addr j, a)` reaches a result, typed by the export's result
  types, with behaviour `b` (`ScalarInstance.ask_ans_iff`).
* `exists_trace_of_sbehaviour`: **closed world**: every terminating Core behaviour of an export
  call against a stateful, nondeterministic host machine `L` (`sbehavioursOf`, Core reduction in
  product with `L`) is the return event of a trace whose export events are that call and return
  and whose import events agree with `L` (adequacy for stateful hosts,
  `ScalarInstance.sadequacy_answers`).
* `exportEvents_map`, `importEvents_map`, `mem_exportEvents_iff`, `mem_importEvents_iff`:
  events of the traces of plays.

What is not grounded at this level: closed-world statements about *import calls*. Adequacy
(M2) relates final behaviours to answers of the closed program; it does not say that a given
Core run makes the import calls of a given trace (under a nondeterministic profile another run
may reach the same result). Properties of import calls hold of the plays of `I.strategy P s`,
which are themselves defined by Core reduction (`Reach P` host-free runs and `resumeResult`).
-/
