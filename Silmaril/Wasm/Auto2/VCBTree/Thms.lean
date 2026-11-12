module

public import Silmaril.Proofs.Wasm.Auto2.VCBTree.Spec

/-!
# The B-tree library's array functions through the VC generator: results

Proofs in `Silmaril.Proofs.Wasm.Auto2.VCBTree.{Conds,Spec}`, for `Silmaril.Wasm.Auto2.VCBTree.Defs`:

* `get_vcs` (2 conditions), `find_vcs` (7 conditions: loop entry, loads, exits, invariant step,
  variant `2^32 - 1 - i`);
* `get_tspec`, `find_tspec`: total correctness against the annotated specifications;
* **`obaSpec_vcgen`**: the specification library's `Silmaril.WasmSpec.BTree.OBASpec`, a second
  solution through the generator. (`btree_search`, `SearchSpec`, stays open: its loop descends a
  tree whose depth is not an `i32` term of the locals, so it has no variant in the generator's
  sense; see `docs/projects/wasm-binaryen-tooling.md`.)
-/

@[expose] public section

/--
info: 'Silmaril.Wasm.Auto2.VCBTree.obaSpec_vcgen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCBTree.obaSpec_vcgen
