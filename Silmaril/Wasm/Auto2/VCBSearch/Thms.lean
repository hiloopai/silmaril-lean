module

public import Silmaril.Proofs.Wasm.Auto2.VCBSearch.Spec

/-!
# `btree_search` through the VC generator: results

Proofs in `Silmaril.Proofs.Wasm.Auto2.VCBSearch.{Tree,Conds,Spec}`, for
`Silmaril.Wasm.Auto2.VCBSearch.Defs`:

* `search_vcs` (14 conditions, partial correctness) and `search_tvcs` (16, total correctness:
  the ghost height of the current page decreases at both descents), `getBA_vcs` (the `BA` contract
  of `oba_get`), `find_vcs'`;
* **`search_spec`**: partial correctness of every instance running `btree_search` against
  `fspec searchFns searchSpecV`, with its callees (`oba_get`, `oba_find`) given by contracts whose
  conditions are proved too; **`search_tspec`**: total correctness against `searchSpecT`;
* **`searchL_valid`**, **`searchLT_valid`**: the library's `Silmaril.WasmSpec.BTree.searchSpec`
  (partial correctness; total correctness with the height bound), with the callees in the store
  added to the precondition. The library's `SearchSpec` itself stays open: its hypothesis gives
  `oba_get` only the `getSpec` contract, which asks for an ordered array, and the child pointers
  are not ordered.
-/

@[expose] public section

/--
info: 'Silmaril.Wasm.Auto2.VCBSearch.searchLT_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Auto2.VCBSearch.searchLT_valid

/--
info: 'Silmaril.Wasm.Auto2.VCBSearch.searchL_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Auto2.VCBSearch.searchL_valid
