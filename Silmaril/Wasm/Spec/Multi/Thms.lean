module

public import Silmaril.Wasm.Spec.Multi.Defs
public import Silmaril.Proofs.Wasm.Spec.Multi.Basic
public import Silmaril.Proofs.Wasm.Spec.Multi.Litmus

@[expose] public section

/-!
# Multi-call specifications: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Multi.{Basic,Litmus}`. Every profile `P`; no determinism is
assumed; the store persists from one export call to the next.

* **`sessionPlay_mem_iff`**: the closed program `I.closedWith P s K` plays the export calls `l`
  (questions and answers, in order) iff `Session P I K s l`: each call is a Core 3.0 run under
  `hostOf I.imports K` from the store left by the previous run (by induction from
  `ScalarInstance.closedWith_after_iff`).
* **`exists_trace_of_session`**: a Core session is the export history of a trace of
  `wasmSem P` whose import events agree with `K`; `session_of_play`: the converse for plays.
* **`exportHist_closed_world`**: an export-history sentence verified in
  `inst exportHist (wasmSem P)` holds of every Core session against every environment;
  `retPost_session`: a return postcondition holds of every call of every session
  (`RetPost.toHist`).
* Litmus: `debugRun_mainFirst`, `earlyDebug_not_mainFirst` (loose semantics, two exports);
  `incProvider_session` (real Core code: every call of every session of the increment provider
  returns one `i32`).

Not covered: stateful environments (`SEnv`) across calls (the environment `K` here is stateless,
as `hostOf`); sessions ending in a pending or divergent call (combine with
`Silmaril.Wasm.Spec.Live`); the component semantics (the reference machine is one call per fresh
instance).
-/
