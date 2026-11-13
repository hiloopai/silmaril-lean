module

public import Silmaril.Wasm.Spec.Harness.Defs
public import Silmaril.Proofs.Wasm.Spec.Harness.Basic
public import Silmaril.Proofs.Wasm.Spec.Harness.Wasm

@[expose] public section

/-!
# Harness reduction: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Harness.{Basic,Wasm}`.

* `Link.of_prefix`, `Good.linkTraces`: linked trace sets of good trace sets are good.
* `sat_link_iff`: the satisfaction condition of `Harness.corridor` (linking with a harness is a
  corridor from linked-system sentences to program properties).
* `ofTrace_sat_linkTraces_iff`: a per-trace sentence about the linked system is the per-trace
  program property `pullTrace`.
* The most general return-postcondition harness (`RetHarness`): `RetHarness.sound` (if every
  linked run passes its checks, every return of `e` satisfies `Q`), `RetHarness.complete` (the
  converse, given a disjoint and injective wiring), `RetHarness.reduce_iff` (exactness on every
  trace set).
* Wasm: `wasm_harness_iff` (**the linkage of the most general harness with a Wasm program never
  calls `assert` with `i32 0` iff export `e` only returns results satisfying `Q`**, every
  profile) and `wasm_harness_closed_world` (then every terminating closed-world Core behaviour of
  `e` against any host machine satisfies `Q`).

Not shown: that `linkTraces` of the traces of two Wasm modules is the trace set of the module
produced by silmaril-lean's static linker. For the closed fragment of `link?` that is M3
(`Silmaril.Wasm.Game.Linking`, `σ_linked = σ_provider ≫ σ_consumer`); relating `Link` with no own
harness imports to `Silmaril.Games.Zip` would transfer it, but a harness with its own `assert` import
is outside `link?`'s fragment (the provider must have no imports and the linked module is closed).
-/
