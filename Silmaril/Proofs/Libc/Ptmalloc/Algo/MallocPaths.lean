module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocLoop
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocSys
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocSmall

/-!
# ptmalloc algorithm: what `Task.algo.bodyMalloc` and `totalMalloc` still need

With the request check, the fastbin and small-bin paths (with their tcache refills), `use_top` and
`sysmalloc`'s `mmap` path proved, `Task.algo.bodyMalloc` and `Task.algo.totalMalloc` rest on the
unsorted scan, the large-bin and bin-map paths, `malloc_consolidate`'s frame and the main-arena
and non-main parts of `sysmalloc`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

/-- **`Task.algo.bodyMalloc`** from the paths still open. -/
theorem bodyMalloc_paths (C : Config) (hscan : Task.algo.mallocScanBody C)
    (hlarge : Task.algo.mallocLargeBody C) (hbm : Task.algo.mallocBinmapBody C)
    (hcons : Task.algo.consolidateBody C) (hmain : Task.algo.sysMainBody C)
    (hheap : Task.algo.sysHeapBody C) : Task.algo.bodyMalloc C :=
  bodyMalloc_of C (mallocFastBody C) (mallocSmallBody C) hscan hlarge hbm hcons
    (sysmallocBody_of C hmain hheap)

/-- **`Task.algo.totalMalloc`** from the paths still open. -/
theorem totalMalloc_paths (C : Config) (hscan : Task.algo.mallocScanBody C)
    (hscanT : Task.algo.mallocScanTotal C) (hbm : Task.algo.mallocBinmapBody C)
    (hcons : Task.algo.consolidateBody C) (hconsT : Task.algo.consolidateTotal C)
    (hmainT : Task.algo.sysMainTotal C) (hheapT : Task.algo.sysHeapTotal C) :
    Task.algo.totalMalloc C :=
  totalMalloc_of C (mallocFastTotal C) hscan hscanT hbm hcons hconsT
    (sysmallocTotal_of C hmainT hheapT)

end Silmaril.Libc.Ptmalloc.Algo
