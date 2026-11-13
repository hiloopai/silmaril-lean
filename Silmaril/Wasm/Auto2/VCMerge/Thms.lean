module

public import Silmaril.Proofs.Wasm.Auto2.VCMerge.Spec

/-!
# `merge` through the VC generator: results

Proofs in `Silmaril.Proofs.Wasm.Auto2.VCMerge.{Conds,Spec}`, for `Silmaril.Wasm.Auto2.VCMerge.Defs`:

* `merge_vcs`: the 33 conditions of `merge` against `mergeSpecV` (two-memory invariants: the
  hand proof's `MFacts` and the copy loop's `CFacts`; total correctness), each closed by a lemma
  over the words of the memories (dispatch: tactic `merge_vc`);
* **`merge_tspec`**: every function instance running `merge` meets `fspec mergeFns mergeSpecV` for
  total correctness (`genFunc_tsound`);
* **`mergeSpec_vcgen`**: the specification library's `Silmaril.WasmSpec.MergeSort.MergeSpec`, a
  second solution through the generator.
-/

@[expose] public section

/--
info: 'Silmaril.Wasm.Auto2.VCMerge.mergeSpec_vcgen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Auto2.VCMerge.mergeSpec_vcgen
