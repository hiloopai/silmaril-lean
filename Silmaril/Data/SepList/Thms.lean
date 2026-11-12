module

public import Silmaril.Proofs.Data.SepList.Dll
public import Silmaril.Proofs.Data.SepList.Ring
public import Silmaril.Proofs.Data.SepList.Skip
public import Silmaril.Proofs.Data.SepList.Slist
public import Silmaril.Proofs.Data.SepList.Frame

/-!
# List segments: theorems

`dllPushFront`, `dllUnlink`, `ringPushFront`, `ringPopFront`, rotation (`holds_ring_rotate`),
`slistPush`, `slistPop`, `skipInsert`, `skipRemove`: each discharges the `Task.seplist.*` of the same name.
In context: `Frag.holds_block_step` (a block's step framed in a larger fragment), `dll_bytes`.
-/
