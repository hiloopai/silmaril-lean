module

public import Silmaril.Proofs.Wasm.Auto2.VCSort.Spec

/-!
# Insertion sort through the VC generator: results

Proofs in `Silmaril.Proofs.Wasm.Auto2.VCSort.{Conds,Spec}`, for `Silmaril.Wasm.Auto2.VCSort.Defs`:

* `sort_vcs`: the 15 conditions of `insertion_sort` against `sortSpecV` (two-memory invariants,
  total correctness), each closed by a lemma over the words of the memories (`c_inner_entry`,
  `place`, `shift`, …) and the hand proof's list lemmas;
* **`sort_tspec`**: every function instance running `insertion_sort` meets
  `fspec sortFns sortSpecV` for total correctness (`genFunc_tsound`);
* **`spec_vcgen`**: the specification library's `Silmaril.WasmSpec.InsertionSort.Spec`, a second
  solution through the generator (`TFSpecAt.conseq`).
-/

@[expose] public section

/--
info: 'Silmaril.Wasm.Auto2.VCSort.spec_vcgen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCSort.spec_vcgen
