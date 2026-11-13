module

public import Silmaril.Wasm.Resource.CompProvider.Defs
public import Silmaril.Proofs.Wasm.Resource.CompProvider.Basic

@[expose] public section

/-!
# Components defining a resource, over several calls: results

Proofs in `Silmaril.Proofs.Wasm.Resource.CompProvider.Basic`, for every core engine, host and
component choice profile:

* **`multiInv_accepts`**: an invariant method (`MultiInv`) for a protocol makes every
  multi-call trace (`refMultiTraces`) accepted;
* **`compProvider_of_ctr`**: a component meeting the counter verification condition `CtrVC`
  (resolved calls do not decrease a measure `ctr`; the constructor returns `own n` with
  `ctr m ≤ n < ctr m'`) satisfies `compProviderSpec new drop` in `refMultiSem`
  (`ctr_multiInv`: `ctrInv ctr` is an invariant method);
* **`compProvider_of_ctrOn`**: the same from `CtrVCOn`, the counter VC asked only from
  configurations satisfying a reachability invariant (`ctrOn_multiInv`; `CtrVC.on`: `CtrVC`
  is the case of the trivial invariant);
* **`compProvider_refuted_of_reuse`**: a component with a multi-call run whose constructor returns
  the same `own n` twice violates `compProviderSpec new drop` in `refMultiSem`
  (`compProvider_reuse_rejected`, by evaluation). In `refSem` the sentence holds of every
  component (`refSem_compProvider`), so this separates the two semantics.

Not done: discharging `CtrVCOn` for a concrete component (it needs the machine runs of its
export calls through `canon lift` of an `own` result). The toy component of
`Silmaril.Wasm.Resource.CompToy` has the executable runs; its buggy variant is refuted.
-/
