module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocScan
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocPaths

/-!
# ptmalloc algorithm: `_int_malloc` with its bin paths proved

`Algo.bodyMalloc_rest`, `Algo.totalMalloc_rest`: `Task.algo.bodyMalloc` and
`Task.algo.totalMalloc` from `bodyMalloc_paths`/`totalMalloc_paths` with the unsorted scan, the
large-bin fit and the bin-map scan proved (`Algo.mallocScanBody`, `mallocScanTotal`,
`mallocLargeBody`, `mallocBinmapBody`): conditional only on `malloc_consolidate` and the two
`sysmalloc` parts.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

/-- **`Task.algo.bodyMalloc`** from `malloc_consolidate` and `sysmalloc`'s two parts. -/
theorem bodyMalloc_rest (C : Config) (hcons : Task.algo.consolidateBody C)
    (hmain : Task.algo.sysMainBody C) (hheap : Task.algo.sysHeapBody C) : Task.algo.bodyMalloc C :=
  bodyMalloc_paths C (mallocScanBody C) (mallocLargeBody C) (mallocBinmapBody C) hcons hmain hheap

/-- **`Task.algo.totalMalloc`** from `malloc_consolidate` and `sysmalloc`'s two parts. -/
theorem totalMalloc_rest (C : Config) (hcons : Task.algo.consolidateBody C)
    (hconsT : Task.algo.consolidateTotal C) (hmainT : Task.algo.sysMainTotal C)
    (hheapT : Task.algo.sysHeapTotal C) : Task.algo.totalMalloc C :=
  totalMalloc_paths C (mallocScanBody C) (mallocScanTotal C) (mallocBinmapBody C) hcons hconsT
    hmainT hheapT

end Silmaril.Libc.Ptmalloc.Algo
