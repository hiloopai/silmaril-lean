module

public import Silmaril.Libc.Ptmalloc.Algo.Tasks.Defs
public import Silmaril.Libc.Ptmalloc.Algo.Leaf.Thms
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.LeafLists
public import Silmaril.Libc.Ptmalloc.Refine.Thms
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Init
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.FreeTcache
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Free
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.World
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.WorldCalls
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Malloc
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocLoop
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocScan
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocSys
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocSmall
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocPaths
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocHeadPaths
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.FreeBody
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocCons
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocHeap
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocSysMain

/-!
# ptmalloc algorithm: theorems

Proved (standard axioms): the leaf lemmas `Algo.leafTcacheGet` (= `Task.algo.leafTcacheGet`),
`Algo.leafTcachePut` (= `Task.algo.leafTcachePut`), `Algo.leafFastPush`, `Algo.leafFastPop`,
`Algo.leafBinRemove`, `Algo.leafBinPushFront`, `Algo.leafUnsortedPush`; `Algo.viewRelabel`
(= `Task.algo.viewRelabel`); the component lemmas (`TcacheSt.wf_get/put`, `FastWF.push/pop`,
`BinsWF.pushSmall/remove/unmark`, `UnsortedWF.push/erase/takeLast`, `TopWF.relabel`,
`TopWF.relabel_coal`); the institution reduction `Algo.safeMF_of_tasks`, its instance `Algo.ptmalloc_safeMF` for the
model, `Algo.initWF` (= `Task.algo.initWF`) and `Algo.ptmalloc_safeMF_init` (from load time);
`Algo.intFree_tcache` (the tcache case of `Task.algo.wfIntFree`, with `Algo.live_tcPut`).

Wave 2 (`Proofs/Libc/Ptmalloc/Algo/{Tiling,Steps,Coalesce,Consolidate,Trim,Free,World}`):
the tiling lemmas (runs, `TopWF.replace`, `TopWF.mergeTop`, `TopSt.locate_of_runs`), the arena
step lemmas, `Algo.wfCoalesce`, `Algo.wfConsolidate`, `Algo.wfSystrim`, `Algo.wfIntFree` (all
three paths), `Algo.liveApart`, `Algo.tidsKept`, `Algo.ptmalloc_safeMF_of` (the institution
reduction for the model, conditional only on `Task.algo.wfWorld` and `Task.algo.mallocTotal`), and
`Algo.wfIntMalloc_of` (`_int_malloc` from `Task.algo.{wfMallocFast, wfMallocSmall, wfMallocLoop}`).
Wave 3 (`Proofs/Libc/Ptmalloc/Algo/{WorldPut,WorldOps,WorldCalls}`): `WorldWF` gains the
kernel link (`covered`, `structs`), `threadArena` and `heaps`; every view has `LocalSp`
(`Algo.localSp`); a body with a `Frame` is put back well formed (`Algo.worldWF_put`) with the
world's live set following the view's (`Algo.put_live`, `put_malloc`, `put_free`); the world
steps (`ptmalloc_init`, `_int_new_arena`, `arena_get`, `arena_get_retry`, `tcache_get`,
`tcache_init`, `markInternal`, `munmap_chunk`) are proved; hence `Algo.wfWorld_of` and
`Algo.mallocTotal_of`: `Task.algo.wfWorld` and `Task.algo.mallocTotal` for the model from the
body obligations `Task.algo.{bodyMalloc, bodyFree, totalMalloc, totalFree}`, and
`Algo.ptmalloc_safeMF_bodies`.
Wave 4 (`Proofs/Libc/Ptmalloc/Algo/FreeBody`): **`Algo.bodyFree`**, **`Algo.totalFree`**
(`_int_free`'s three paths with a `Frame`: `ArenaStep`/`ConsStep` gain a byte cover, `systrim`
gives back only top bytes, `coalesce`/`malloc_consolidate`/`heap_trim` do not abort), hence
`Algo.ptmalloc_safeMF_mallocBodies` (conditional only on `Task.algo.{bodyMalloc, totalMalloc}`).
Open: the other per-body obligations of `Silmaril.Libc.Ptmalloc.Algo.Tasks.Defs` and the design's
`Task.algo.*` (`wfIntMalloc`, `noAbort`, `wfWorld`, `mallocTotal`, …).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

/-- **`Algo.viewRelabel`**. -/
theorem viewRelabel : Task.algo.viewRelabel :=
  fun ts a u p hc hu => ts.view_relabel a u p hc hu

/-- **The algorithm model is a model of the institution's `safe` sentence** (malloc/free, with
ghost tokens) from any well-formed load-time world, given the world-level obligations. -/
theorem ptmalloc_safeMF (C : Config) (hC : C.Ok) (tid : Nat) (w0 : World)
    (hwf : Task.algo.wfWorld C (ptmalloc C)) (htot : Task.algo.mallocTotal C (ptmalloc C))
    (hap : Task.algo.liveApart C) (htid : Task.algo.tidsKept C (ptmalloc C))
    (h0 : WorldWF C w0) (ht0 : tid ∈ w0.tids) (hl0 : w0.live C = []) :
    SafeMF C (ptmalloc C) tid w0 (RefInv C tid) :=
  safeMF_of_tasks C (ptmalloc C) hC tid w0 hwf htot hap htid h0 ht0 hl0

/-- **From load time**: the model, started in `initWorld` (break page-aligned, at least a page),
is a model of the institution's `safe` sentence on `malloc`/`free`, given the open world-level
obligations. -/
theorem ptmalloc_safeMF_init (C : Config) (hC : C.Ok) (ma tid brk : Nat) (o : KOracle)
    (hma : ma ≠ 0) (hpg : C.page ≤ brk) (hbrk : brk % C.page = 0)
    (hwf : Task.algo.wfWorld C (ptmalloc C)) (htot : Task.algo.mallocTotal C (ptmalloc C))
    (hap : Task.algo.liveApart C) (htid : Task.algo.tidsKept C (ptmalloc C)) :
    SafeMF C (ptmalloc C) tid (initWorld C ma tid brk o) (RefInv C tid) :=
  have ⟨h0, hl0⟩ := initWF C hC ma tid brk o hma hpg hbrk
  ptmalloc_safeMF C hC tid _ hwf htot hap htid h0 (by simp [initWorld]) hl0

/-- **From load time, conditional only on the two world-level obligations**: `liveApart` and
`tidsKept` are proved (`Algo.liveApart`, `Algo.tidsKept`). -/
theorem ptmalloc_safeMF_of (C : Config) (hC : C.Ok) (ma tid brk : Nat) (o : KOracle)
    (hma : ma ≠ 0) (hpg : C.page ≤ brk) (hbrk : brk % C.page = 0)
    (hwf : Task.algo.wfWorld C (ptmalloc C)) (htot : Task.algo.mallocTotal C (ptmalloc C)) :
    SafeMF C (ptmalloc C) tid (initWorld C ma tid brk o) (RefInv C tid) :=
  ptmalloc_safeMF_init C hC ma tid brk o hma hpg hbrk hwf htot (liveApart C) (tidsKept C)

/-- **From load time, conditional only on the body obligations** (`_int_malloc` and `_int_free`
on a view with its spatial facts: well formed after, a `Frame`, no abort). -/
theorem ptmalloc_safeMF_bodies (C : Config) (hC : C.Ok) (ma tid brk : Nat) (o : KOracle)
    (hma : ma ≠ 0) (hpg : C.page ≤ brk) (hbrk : brk % C.page = 0)
    (hB : Task.algo.bodyMalloc C) (hF : Task.algo.bodyFree C) (htM : Task.algo.totalMalloc C)
    (htF : Task.algo.totalFree C) :
    SafeMF C (ptmalloc C) tid (initWorld C ma tid brk o) (RefInv C tid) :=
  ptmalloc_safeMF_of C hC ma tid brk o hma hpg hbrk (wfWorld_of C hB hF) (mallocTotal_of C hB htM htF)

/-- **From load time, conditional only on `_int_malloc`'s body obligations** (`_int_free`'s are
`Algo.bodyFree`, `Algo.totalFree`). -/
theorem ptmalloc_safeMF_mallocBodies (C : Config) (hC : C.Ok) (ma tid brk : Nat) (o : KOracle)
    (hma : ma ≠ 0) (hpg : C.page ≤ brk) (hbrk : brk % C.page = 0)
    (hB : Task.algo.bodyMalloc C) (htM : Task.algo.totalMalloc C) :
    SafeMF C (ptmalloc C) tid (initWorld C ma tid brk o) (RefInv C tid) :=
  ptmalloc_safeMF_bodies C hC ma tid brk o hma hpg hbrk hB (bodyFree C) htM (totalFree C)

end Silmaril.Libc.Ptmalloc.Algo
