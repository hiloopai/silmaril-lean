module

public import Silmaril.Proofs.Wasm.Auto2.VCMSort.Spec

/-!
# Merge sort through the VC generator: results

Proofs in `Silmaril.Proofs.Wasm.Auto2.VCMSort.{Conds,Spec}`, for `Silmaril.Wasm.Auto2.VCMSort.Defs`:

* `msort_vcs N`: the 5 conditions of `merge_sort` against `msortSpec` under `msFns N` (base
  case, the two recursive calls' and `merge`'s preconditions, `sorts_compose`), for every `N`;
* **`msort_tspec`**: total correctness of every instance of `merge_sort` that is its own function
  `1`, by the generator's recursion theorem `Silmaril.Wasm.Auto2.VCGen.genFunc_tsound_rec`;
* **`spec_vcgen`**: the specification library's `Silmaril.WasmSpec.MergeSort.Spec`, a second
  solution through the generator (with `merge` from `Silmaril.Wasm.Auto2.VCMerge`).
-/

@[expose] public section

/--
info: 'Silmaril.Wasm.Auto2.VCMSort.spec_vcgen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Auto2.VCMSort.spec_vcgen
