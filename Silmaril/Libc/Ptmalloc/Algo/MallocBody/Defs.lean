module

public import Silmaril.Libc.Ptmalloc.Algo.Tasks.Defs

/-!
# ptmalloc algorithm: `Task.algo.bodyMalloc` and `totalMalloc`, path by path

`Task.algo.bodyMalloc` and `Task.algo.totalMalloc` (`Silmaril.Libc.Ptmalloc.Algo.Tasks.Defs`) speak
of the whole of `_int_malloc`. Here they are split along `intMalloc`'s paths
(`Silmaril.Libc.Ptmalloc.Algo.Malloc.Defs`), every piece over a view with its spatial facts
(`LocalWF ∧ LocalSp`) and with a `Frame`:

| obligation | path |
|---|---|
| `mallocFastBody`, `mallocFastTotal` | `mallocFast` (fastbin hit, tcache refill) |
| `mallocSmallBody` | `mallocSmall` (small-bin hit, tcache refill) |
| `mallocScanBody`, `mallocScanTotal` | `unsortedScan` (with `return_cached`) |
| `mallocLargeBody` | `largeFit` + `takeFit` |
| `mallocBinmapBody` | `binmapScan` + `takeFit` |
| `consolidateBody`, `consolidateTotal` | `malloc_consolidate` (the large request's, and the loop's retry) |
| `sysmallocBody`, `sysmallocTotal` | `sysmalloc` |

The request check (`ENOMEM`) and `use_top` are proved outright, and the combination
(`Algo.bodyMalloc_of`, `Algo.totalMalloc_of`, `Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocBody`) needs
nothing else. A piece that returns nothing yet (the scan going on, the bin-map scan finding
nothing, `malloc_consolidate`) is an `MStep`: the live set kept up to order, with a `Frame`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

/-- **The conclusion of `Task.algo.bodyMalloc`** for a run of `_int_malloc` (or of one of its
paths) from `l` to `l'` returning `p` for a request of `n` bytes. -/
def MBody (C : Config) (n : Nat) (l : Local) (p : Nat) (l' : Local) : Prop :=
  MallocOK C n l p l' ∧ Frame C l l' [] ∧ KeptAway l l' ∧
    (l.thread.tcache = none → l'.thread.tcache = none)

/-- **A step of `_int_malloc` that returns nothing yet**: well formed after, the live set kept up
to order, with a `Frame`. -/
def MStep (C : Config) (l l' : Local) : Prop :=
  LocalWF C l' ∧ (l'.live C).Perm (l.live C) ∧ Frame C l l' [] ∧ KeptAway l l' ∧
    (l.thread.tcache = none → l'.thread.tcache = none)

/-- **The fastbin path** (`mallocFast`, with its tcache refill). -/
def Task.algo.mallocFastBody (C : Config) : Prop :=
  C.Ok → ∀ l l' n nb p, LocalWF C l → LocalSp C l → C.checkedRequest2size n = some nb →
    nb ≤ C.maxFast → mallocFast C l nb = .ok (some (p, l')) → MBody C n l p l'

/-- The fastbin path does not abort (`malloc(): unaligned fastbin chunk detected`,
`malloc(): memory corruption (fast)`). -/
def Task.algo.mallocFastTotal (C : Config) : Prop :=
  C.Ok → ∀ l n nb, LocalWF C l → LocalSp C l → C.checkedRequest2size n = some nb →
    nb ≤ C.maxFast → ∃ r, mallocFast C l nb = .ok r

/-- **The small-bin path** (`mallocSmall`, with its tcache refill). -/
def Task.algo.mallocSmallBody (C : Config) : Prop :=
  C.Ok → ∀ l l' n nb p, LocalWF C l → LocalSp C l → C.checkedRequest2size n = some nb →
    C.inSmallRange nb = true → mallocSmall C l nb = some (p, l') → MBody C n l p l'

/-- **The unsorted scan**, as `mallocLoop` calls it: a returned chunk, `return_cached` (the
tcache bin then has a chunk to return), or going on (an `MStep` that leaves the fastbins). -/
def Task.algo.mallocScanBody (C : Config) : Prop :=
  C.Ok → ∀ l l' n nb r, LocalWF C l → LocalSp C l → C.checkedRequest2size n = some nb →
    unsortedScan C nb (tcOn C l (C.tidx nb)) l.av.unsorted.list.length 0 false 0 l = .ok (r, l') →
    match r with
    | .done p => MBody C n l p l'
    | .cached => ∃ p l'', l'.tcacheGet C (C.tidx nb) = some (p, l'') ∧ MBody C n l p l''
    | .cont => MStep C l l' ∧ l'.av.fast = l.av.fast

/-- The unsorted scan does not abort. -/
def Task.algo.mallocScanTotal (C : Config) : Prop :=
  C.Ok → ∀ l n nb, LocalWF C l → LocalSp C l → C.checkedRequest2size n = some nb →
    ∃ r, unsortedScan C nb (tcOn C l (C.tidx nb)) l.av.unsorted.list.length 0 false 0 l = .ok r

/-- **The large-bin best fit** (a large request). -/
def Task.algo.mallocLargeBody (C : Config) : Prop :=
  C.Ok → ∀ l n nb v, LocalWF C l → LocalSp C l → C.checkedRequest2size n = some nb →
    C.inSmallRange nb = false → largeFit C l nb = some v →
    MBody C n l (takeFit C l v (C.binIndex nb) nb false).1 (takeFit C l v (C.binIndex nb) nb false).2

/-- **The bin-map scan**: a fitting chunk taken, or nothing found (an `MStep` that leaves the
fastbins). -/
def Task.algo.mallocBinmapBody (C : Config) : Prop :=
  C.Ok → ∀ l l₁ n nb o, LocalWF C l → LocalSp C l → C.checkedRequest2size n = some nb →
    binmapScan C C.nBins (C.binIndex nb + 1) l = (o, l₁) →
    match o with
    | some (v, j) =>
      MBody C n l (takeFit C l₁ v j nb (C.inSmallRange nb)).1 (takeFit C l₁ v j nb (C.inSmallRange nb)).2
    | none => MStep C l l₁ ∧ l₁.av.fast = l.av.fast

/-- **`malloc_consolidate`** as an `MStep`, clearing `have_fastchunks`. -/
def Task.algo.consolidateBody (C : Config) : Prop :=
  C.Ok → ∀ l l', LocalWF C l → LocalSp C l → consolidate C l = .ok l' →
    MStep C l l' ∧ l'.av.fast.haveFast = false

/-- `malloc_consolidate` does not abort. -/
def Task.algo.consolidateTotal (C : Config) : Prop :=
  C.Ok → ∀ l, LocalWF C l → LocalSp C l → ∃ l', consolidate C l = .ok l'

/-- **`sysmalloc`**, called when the top chunk cannot serve `nb` (after `ptmalloc_init`). -/
def Task.algo.sysmallocBody (C : Config) : Prop :=
  C.Ok → ∀ l l' n nb p, LocalWF C l → LocalSp C l → l.shared.init = true →
    C.checkedRequest2size n = some nb →
    topSz l.av.tiles < nb + C.minSize → sysmalloc C l nb = .ok (p, l') → MBody C n l p l'

/-- `sysmalloc` does not abort. -/
def Task.algo.sysmallocTotal (C : Config) : Prop :=
  C.Ok → ∀ l n nb, LocalWF C l → LocalSp C l → C.checkedRequest2size n = some nb →
    topSz l.av.tiles < nb + C.minSize → ∃ r, sysmalloc C l nb = .ok r

/-! ## `sysmalloc`, part by part

`Algo.sysmallocBody_of`, `Algo.sysmallocTotal_of`: `sysmallocBody` and `sysmallocTotal` from the
proved `mmap` path (`Algo.sysmallocMmap_body`, `sysmallocMmap_none`) and the two parts after it. -/

/-- **`sysmalloc`'s main-arena part** (`sbrk`, the `mmap` fallback, the new top, the final carve). -/
def Task.algo.sysMainBody (C : Config) : Prop :=
  C.Ok → ∀ l l' n nb p, LocalWF C l → LocalSp C l → l.shared.init = true → l.isMain = true →
    C.checkedRequest2size n = some nb → topSz l.av.tiles < nb + C.minSize →
    sysmallocMain C l nb = .ok (p, l') → MBody C n l p l'

/-- `sysmalloc`'s main-arena part does not abort. -/
def Task.algo.sysMainTotal (C : Config) : Prop :=
  C.Ok → ∀ l n nb, LocalWF C l → LocalSp C l → l.isMain = true →
    C.checkedRequest2size n = some nb → topSz l.av.tiles < nb + C.minSize →
    ∃ r, sysmallocMain C l nb = .ok r

/-- **`sysmalloc`'s non-main part** (`grow_heap`, `new_heap`, the `mmap` last resort, the carve). -/
def Task.algo.sysHeapBody (C : Config) : Prop :=
  C.Ok → ∀ l l' n nb p tried, LocalWF C l → LocalSp C l → l.shared.init = true →
    l.isMain = false → C.checkedRequest2size n = some nb → topSz l.av.tiles < nb + C.minSize →
    sysmallocHeap C l nb tried = .ok (p, l') → MBody C n l p l'

/-- `sysmalloc`'s non-main part does not abort. -/
def Task.algo.sysHeapTotal (C : Config) : Prop :=
  C.Ok → ∀ l n nb tried, LocalWF C l → LocalSp C l → l.isMain = false →
    C.checkedRequest2size n = some nb → topSz l.av.tiles < nb + C.minSize →
    ∃ r, sysmallocHeap C l nb tried = .ok r

end Silmaril.Libc.Ptmalloc.Algo
