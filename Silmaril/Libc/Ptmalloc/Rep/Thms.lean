module

public import Silmaril.Proofs.Libc.Ptmalloc.Seplist.Frame
public import Silmaril.Proofs.Libc.Ptmalloc.Seplist.Tcache
public import Silmaril.Proofs.Libc.Ptmalloc.Seplist.Leaf

/-!
# ptmalloc, representation: theorems

`Seplist.localFrame`, `Seplist.localRep_of_check` (the executable `LocalRep.check` is sound), `Seplist.leafTcacheGet`; leaf store lemmas `Seplist.leafFastPush`, `leafFastPop`, `leafTcachePut` (and the generic
`Silmaril.Data.Frag.holds_update_perm`).
-/
