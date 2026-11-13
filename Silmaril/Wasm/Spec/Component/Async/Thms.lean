module

public import Silmaril.Wasm.Spec.Component.Async.Defs
public import Silmaril.Proofs.Wasm.Spec.Component.Async

@[expose] public section

/-!
# Streams and async calls: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Component.Async`.

* `mapP_not_closes`, `mapP_not_writes`: synchronous events carry no stream traffic;
* `syncToAsync_streamSafe`, `syncToAsync_closedExactlyOnce`: every synchronous program (of any
  synchronous component semantics: the IR, the reference) satisfies the stream logics after
  embedding.

The comorphism `syncCoHom` and the logic map `StreamSafe.toAct` are in
`Silmaril.Wasm.Spec.Component.Async.Defs`.
-/
