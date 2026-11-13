module

public import Silmaril.Proofs.Wasm.Logic.Iris.Heap
public import Silmaril.Proofs.Wasm.Logic.Iris.Cells

/-!
# Ghost state for the Iris logic of Wasm Core 3.0: theorems

The ghost heap (`Silmaril.Wasm.Logic.Iris.Heap.Defs`) against the store
(`Silmaril/Proofs/Wasm/Logic/Iris/{Heap,Cells}.lean`):

* `interp_lookup`, `interp_lookup_cells`: owned cells are the store's;
* `interp_change`: the state interpretation follows a change of the store that
  updates owned cells, allocates fresh cells and keeps all others (a `Change`);
* `genHeap_update_cells`, `genHeap_alloc_cells`: the ghost-heap updates behind it;
* the cells after each store update of the state instructions:
  `cellOf_setGlobal_*`, `cellOf_setMem_*`, `cellOf_setTable_*`,
  `cellOf_setStructField_*`, `cellOf_setArrayField_*`, `cellOf_addStruct_*`,
  `cellOf_addArray_*`, `cellOf_frame_ne`; `bytes_of_cells` (owned bytes are the
  bytes of the memory).
-/