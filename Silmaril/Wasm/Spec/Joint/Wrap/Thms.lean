module

public import Silmaril.Wasm.Spec.Joint.Wrap.Defs
public import Silmaril.Proofs.Wasm.Spec.Joint.Wrap

@[expose] public section

/-!
# Wrapping core modules as components: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Joint.Wrap`. Every profile `P`, no determinism assumption.

* `wrapFn_injective`, so `wrapCoHom L P` is a model-expansive comorphism from pulled component
  specifications of numeric Core 3.0 modules to component specifications of wrapped modules
  (`pushCoHom_modelExpansive`, `push_entails_iff`).
* The canonical ABI at the wrapping types (`numVT`: `i32 ↦ u32`, `i64 ↦ u64`, floats kept):
  `checkLower_numToIR`, `liftArgs_numToIR`, `map_toRefVal_numToIR`, and
  `liftOutcome_resOut` (the canonical-ABI outcome of a typed Core result is `wrapOut` of its
  behaviour: uncaught exceptions become traps).
* The wrapping component: `wrapSimple_good` (it is in the fragment of the IR soundness link,
  given distinct export names), `cface_wrapSimple` (**its interface is the image of the module
  interface under `wrapFn`**), `wrapSimple_getElem`.
* `wrap_spec`: a first call of export `j` of a Core 3.0 instance of `m` returning `b` gives the
  outcome `wrapOut b` of the canonical-ABI specification of the wrapping component.
* `wrap_sound`: **soundness of wrapping w.r.t. the boundary adapters**: every terminating first
  call of the module, translated by the change of base, is a trace of the wrapping component in
  Silmaril's IR (`irSem (modSem P)`, whose boundary is `canon lift`).
* `wrap_contract`: hence a contract verified on the wrapping component in the IR holds of the
  module's terminating first calls.

Not covered: later calls on the same instance, divergence, imports (`NumModule`s are
import-free), and the converse inclusion (IR traces of the wrapping component are wrapped
module traces), which would need Core type soundness for results.
-/
