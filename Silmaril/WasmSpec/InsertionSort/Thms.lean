module

public import Silmaril.Proofs.WasmSpec.InsertionSort.Tactic
public import Silmaril.Proofs.WasmSpec.InsertionSort.Tests

/-!
# Wasm specification library: `InsertionSort` v1, results

Solutions (see `manifest.toml`):

* `tactic`: `spec_tactic : Spec` and `specStore_tactic : SpecStore`
  (`Silmaril.Proofs.WasmSpec.InsertionSort.Tactic`): symbolic execution over the `i32` view of
  `Silmaril.Wasm.Logic.Words`, an outer invariant (`OInv`: a permutation of the input, equal
  outside the segment, sorted prefix of length `i`; variant `n + 1 - i`) and an inner one
  (`IInv`: the words are `hole ys i j`, the shifted elements exceed `key`; variant `j`), with
  the list lemmas of `Silmaril.Proofs.WasmSpec.InsertionSort.Lists` (`hole_shift`,
  `hole_place_perm`, `hole_place_sorted`); **every-run total correctness**
  (`Silmaril.Wasm.Logic.Hoare.TFSpecAt`), at every profile and for every host relation.

Tested (`Silmaril.Proofs.WasmSpec.InsertionSort.Tests`, `#guard`, not proofs): runs of the
instantiated module with silmaril-lean's verified interpreter sort pseudo-random arrays as
`List.mergeSort` does and leave every other byte of memory unchanged.

Canonical results: `spec : Spec`, `specStore : SpecStore`.
-/

@[expose] public section

namespace Silmaril.WasmSpec.InsertionSort

/-- The canonical solution of `Spec`. -/
theorem spec : Spec := spec_tactic

/-- The canonical solution of `SpecStore`. -/
theorem specStore : SpecStore := specStore_tactic

end Silmaril.WasmSpec.InsertionSort

/-- info: 'Silmaril.WasmSpec.InsertionSort.spec_tactic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.InsertionSort.spec_tactic

/-- info: 'Silmaril.WasmSpec.InsertionSort.specStore_tactic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.InsertionSort.specStore_tactic

/-- info: 'Silmaril.WasmSpec.InsertionSort.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.InsertionSort.spec

/-- info: 'Silmaril.WasmSpec.InsertionSort.specStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.WasmSpec.InsertionSort.specStore
