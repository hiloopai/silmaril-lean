module

public import Silmaril.Proofs.WasmSpec.MergeSort.Tactic
public import Silmaril.Proofs.WasmSpec.MergeSort.Tests

/-!
# Wasm specification library: `MergeSort` v1, results

Solutions (see `manifest.toml`), all `tactic`, **every-run total correctness**
(`Silmaril.Wasm.Logic.Hoare.TFSpecAt`) at every profile and for every host relation:

* `mergeSpec_tactic : MergeSpec` (`Silmaril.Proofs.WasmSpec.MergeSort.Merge`): the merge loop
  (`MInv`: the buffer's prefix is a sorted permutation of the taken elements, below the rest;
  list lemmas `merge_left`, `merge_right`) and the copy loop (`CInv`);
* `spec_tactic : Spec` (`Silmaril.Proofs.WasmSpec.MergeSort.Tactic`): recursion by induction on a
  bound of the length (`sort_below`, `FSpec.below`), the call rule over the `i32` view
  (`Silmaril.Wasm.Logic.Words.t_call`) for the two recursive calls and the merge, `sorts_compose`;
* `specStore_tactic : SpecStore`: the instantiated module.

Tested (`#guard` in `Silmaril.Proofs.WasmSpec.MergeSort.Tests`, and `wasmi` property tests in
`tools/wasm-spec-fuzz`; not proofs).

Canonical results: `mergeSpec`, `spec`, `specStore`.
-/

@[expose] public section

namespace Silmaril.WasmSpec.MergeSort

/-- The canonical solution of `MergeSpec`. -/
theorem merge_spec : MergeSpec := mergeSpec_tactic

/-- The canonical solution of `Spec`. -/
theorem spec : Spec := spec_tactic

/-- The canonical solution of `SpecStore`. -/
theorem specStore : SpecStore := specStore_tactic

end Silmaril.WasmSpec.MergeSort

/-- info: 'Silmaril.WasmSpec.MergeSort.mergeSpec_tactic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.WasmSpec.MergeSort.mergeSpec_tactic

/-- info: 'Silmaril.WasmSpec.MergeSort.spec_tactic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.WasmSpec.MergeSort.spec_tactic

/-- info: 'Silmaril.WasmSpec.MergeSort.specStore_tactic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.WasmSpec.MergeSort.specStore_tactic

/-- info: 'Silmaril.WasmSpec.MergeSort.merge_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.WasmSpec.MergeSort.merge_spec

/-- info: 'Silmaril.WasmSpec.MergeSort.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.WasmSpec.MergeSort.spec

/-- info: 'Silmaril.WasmSpec.MergeSort.specStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.WasmSpec.MergeSort.specStore
