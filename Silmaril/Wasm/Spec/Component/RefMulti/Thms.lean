module

public import Silmaril.Wasm.Spec.Component.RefMulti.Defs
public import Silmaril.Proofs.Wasm.Spec.Component.RefMulti

@[expose] public section

/-!
# Several export calls on one reference instance: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Component.RefMulti`, for every core engine, host, host state
and component choice profile:

* `refMultiTraces_good` (in `Defs`): the multi-call traces are good, so `refMultiSem` is a
  semantics of the specification format;
* **`refTraces_eq_short`**: `refTraces prof h σ0 p = {t | t ∈ refMultiTraces prof h σ0 p ∧
  t.length ≤ 2}`: `refSem` is the one-call restriction of `refMultiSem`, so the per-call
  `exportBehaviours` are exactly the one-call prefixes (`refTraces_sub_refMulti`,
  `refMulti_short`);
* `doneEvents_mem`: the events of every run of resolved calls (`RunCalls`) after an
  instantiation are a multi-call trace; `RunCalls.append`: runs compose.
-/
