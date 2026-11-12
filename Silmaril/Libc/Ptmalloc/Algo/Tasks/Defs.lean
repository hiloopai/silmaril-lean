module

public import Silmaril.Libc.Ptmalloc.Algo.Impl.Defs
public import Silmaril.Libc.Ptmalloc.Refine.Defs

/-!
# ptmalloc algorithm: the per-body obligations of `ptmalloc C`

The design's obligations (`Task.algo.{noAbort, wfIntMalloc, wfIntFree, wfWorld, mallocTotal}`,
`Silmaril.Libc.Ptmalloc.Algo.Defs`) split along the bodies of `Silmaril.Libc.Ptmalloc.Algo.*`, so
that each can be proved in its own module, from the step and leaf lemmas, mentioning only the
components the body touches. Every statement is for all `C` with `C.Ok`.

| obligation | body | components |
|---|---|---|
| `wfCoalesce` | `coalesce` (shared by `_int_free` and `malloc_consolidate`) | Top, Bins, Unsorted |
| `wfConsolidate` | `malloc_consolidate` | Fastbins, Top, Bins, Unsorted |
| `wfSystrim` | `systrim` | Top, Kernel |
| `wfIntFree` (design) | `_int_free` | Tcache, Fastbins, … |
| `wfSysmalloc` | `sysmalloc` | Top, Mmap, Kernel, (free of the old top) |
| `wfIntMalloc` (design) | `_int_malloc` | all |
| `wfIntRealloc` | `_int_realloc` | Top, Bins, Unsorted (+ `_int_malloc`, `_int_free`) |
| `wfMmapped` | `munmap_chunk`, `mremap_chunk`, `sysmalloc_mmap` | Mmap, Kernel |
| `initWF` | `initWorld` | — |
| `wfCallocRealloc` | `__libc_calloc`, `__libc_realloc` | world |
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

/-- Only the arena changes. -/
abbrev fpArena : Footprint := { thread := false, shared := false, kernel := false }

/-- **`Task.algo.wfCoalesce`**: coalescing a held (`internal`) chunk keeps `LocalWF`, changes only
the arena, and leaves the lent-out payloads unchanged. -/
def Task.algo.wfCoalesce (C : Config) : Prop :=
  C.Ok → ∀ l l' a s, LocalWF C l → (∃ c ∈ l.av.chunks, c.addr = a ∧ c.use = .internal) →
    coalesce l a = .ok (s, l') →
    LocalWF C l' ∧ Footprint.Within fpArena l l' ∧ (l'.av.out C).Perm (l.av.out C)

/-- **`Task.algo.wfConsolidate`**: `malloc_consolidate` keeps `LocalWF`, changes only the arena,
leaves the lent-out payloads unchanged and empties every fastbin. -/
def Task.algo.wfConsolidate (C : Config) : Prop :=
  C.Ok → ∀ l l', LocalWF C l → consolidate C l = .ok l' →
    LocalWF C l' ∧ Footprint.Within fpArena l l' ∧ (l'.av.out C).Perm (l.av.out C) ∧
      ∀ i, l'.av.fast.lists i = []

/-- **`Task.algo.wfSystrim`**: `systrim` keeps `LocalWF` (M7: called with
`chunksize (top) ≥ mp_.trim_threshold`) and changes only the arena's top and the break. -/
def Task.algo.wfSystrim (C : Config) : Prop :=
  C.Ok → ∀ l l' pad, LocalWF C l → l.isMain = true →
    l.shared.mm.mp.trimThreshold ≤ l.av.tiles.topSize → systrim C l pad = .ok l' →
    LocalWF C l' ∧ Footprint.Within { thread := false, shared := false } l l' ∧
      l'.av.out C = l.av.out C

/-- **`Task.algo.wfSysmalloc`**: `sysmalloc` (called when top cannot serve `nb`) keeps
`LocalWF` and changes the live set as a `malloc` of `nb - SIZE_SZ` bytes. -/
def Task.algo.wfSysmalloc (C : Config) : Prop :=
  C.Ok → ∀ l l' nb p, LocalWF C l → nb % C.align = 0 → C.minSize ≤ nb →
    topSz l.av.tiles < nb + C.minSize → sysmalloc C l nb = .ok (p, l') →
    LocalWF C l' ∧ Footprint.Within {} l l' ∧ MallocLive C (nb - C.sizeSz) p (l.live C) (l'.live C)

/-- **`Task.algo.wfIntRealloc`**: `_int_realloc` of a live payload keeps `LocalWF`; on success the
old payload is replaced by a new one of at least `nb - SIZE_SZ` bytes, on failure nothing
changes in the live set. -/
def Task.algo.wfIntRealloc (C : Config) : Prop :=
  C.Ok → ∀ l l' oldp oldsize nb q u, LocalWF C l → (oldp + C.hdr, u) ∈ l.live C →
    l.av.tiles.sizeAt oldp = oldsize → intRealloc C l oldp oldsize nb = .ok (q, l') →
    LocalWF C l' ∧ Footprint.Within {} l l' ∧
      MallocLive C (nb - C.sizeSz) q ((l.live C).erase (oldp + C.hdr, u))
        (if q = 0 then (l'.live C).erase (oldp + C.hdr, u) else l'.live C)

/-- **`Task.algo.wfMmapped`**: the `mmap`ed-chunk bodies change only the shared part and the
kernel, keep `LocalWF`, and move exactly their chunk in the live set. -/
def Task.algo.wfMmapped (C : Config) : Prop :=
  C.Ok → ∀ l, LocalWF C l →
    (∀ nb p l', sysmallocMmap C l nb = (some p, l') →
      LocalWF C l' ∧ Footprint.Within { arena := false, thread := false } l l' ∧
        MallocLive C (nb - C.sizeSz) p (l.live C) (l'.live C)) ∧
    (∀ c u l', (c + C.hdr, u) ∈ l.shared.live C → munmapChunk C l c = .ok l' →
      LocalWF C l' ∧ Footprint.Within { arena := false, thread := false } l l' ∧
        (l'.live C).Perm ((l.live C).erase (c + C.hdr, u)))

/-- **`Task.algo.initWF`**: the load-time world is well formed and has no live payload (break
page-aligned and at least a page; `main_arena` not null). -/
def Task.algo.initWF (C : Config) : Prop :=
  C.Ok → ∀ ma tid brk o, ma ≠ 0 → C.page ≤ brk → brk % C.page = 0 →
    WorldWF C (initWorld C ma tid brk o) ∧ (initWorld C ma tid brk o).live C = []

/-- **`Task.algo.wfCallocRealloc`**: `calloc` and `realloc` keep `WorldWF` and change the live set
as `allocLoose` allows (calloc: a `malloc`; realloc: a move, a failure keeping the block, or a
free for `n = 0`). -/
def Task.algo.wfCallocRealloc (C : Config) (A : Ops C) : Prop :=
  C.Ok → ∀ w tid, WorldWF C w → tid ∈ w.tids →
    (∀ k m p w', A.calloc w tid k m = .ok (p, w') →
      WorldWF C w' ∧ MallocLive C (k * m) p (w.live C) (w'.live C)) ∧
    (∀ p u n q w', (p, u) ∈ w.live C → A.realloc w tid p n = .ok (q, w') →
      WorldWF C w' ∧
        ((n = 0 ∧ q = 0 ∧ (w'.live C).Perm ((w.live C).erase (p, u))) ∨
         (n ≠ 0 ∧ q = 0 ∧ (w'.live C).Perm (w.live C)) ∨
         (n ≠ 0 ∧ q ≠ 0 ∧ MallocLive C n q ((w.live C).erase (p, u)) (w'.live C))))

/-- **A successful `_int_malloc` path from `l` to `l'` returning `p` for a request of `n` bytes**:
well formed after, the arena index and kind kept, the live set changed as `MallocLive` says. -/
def MallocOK (C : Config) (n : Nat) (l : Local) (p : Nat) (l' : Local) : Prop :=
  LocalWF C l' ∧ Footprint.Within {} l l' ∧ MallocLive C n p (l.live C) (l'.live C)

/-- **`Task.algo.wfMallocFast`**: the fastbin path (with its tcache refill). -/
def Task.algo.wfMallocFast (C : Config) : Prop :=
  C.Ok → ∀ l l' n nb p, LocalWF C l → C.checkedRequest2size n = some nb → nb ≤ C.maxFast →
    mallocFast C l nb = .ok (some (p, l')) → MallocOK C n l p l'

/-- **`Task.algo.wfMallocSmall`**: the small-bin path (with its tcache refill). -/
def Task.algo.wfMallocSmall (C : Config) : Prop :=
  C.Ok → ∀ l l' n nb p, LocalWF C l → C.checkedRequest2size n = some nb → C.inSmallRange nb = true →
    mallocSmall C l nb = some (p, l') → MallocOK C n l p l'

/-- **`Task.algo.wfMallocLoop`**: the main loop (unsorted scan, large-bin fit, bin-map scan,
`use_top`, consolidation and retry, `sysmalloc`). -/
def Task.algo.wfMallocLoop (C : Config) : Prop :=
  C.Ok → ∀ l l' n nb p, LocalWF C l → C.checkedRequest2size n = some nb →
    mallocLoop C nb 3 l = .ok (p, l') → MallocOK C n l p l'

/-! ## The world-facing footprint of a body (wave 3)

`Task.algo.wfWorld` is the frame of `World.put` over the body obligations. `LocalWF` speaks of one
view, so a body must also say what it does to the rest of the world: `Frame` is that, and every
clause is local (about `l`, `l'` only). -/

/-- **What a body run from `l` to `l'` does to the rest of the world** (`freed`: the payloads it
frees, `[]` for `malloc`):
* `spatial`: a range of the process's memory apart from the view's spans stays the process's and
  apart from the new spans (new spans come from old ones or fresh kernel memory, and the kernel
  gives back only the view's own memory);
* `covered`: the new spans are the process's memory;
* non-main bodies leave the break and `mp_.sbrk_base` alone; no body touches `brkStart`, the
  init flag, the arena list or `thread_arena`; a heap is never lost;
* `clients`: every lent-out chunk of the arena, except the freed ones, stays a chunk;
* `fresh`: a new tcache entry is a lent-out chunk of the arena, freed now or not lent out before. -/
structure Frame (C : Config) (l l' : Local) (freed : List (Nat × Nat)) : Prop where
  avAddr : l'.avAddr = l.avAddr
  isMain : l'.isMain = l.isMain
  spatial : ∀ r, 0 < r.2 → l.kernel.Covers r → Away l.spans r →
    l'.kernel.Covers r ∧ Away l'.spans r
  covered : ∀ r ∈ l'.spans, l'.kernel.Covers r
  brkStart : l'.kernel.brkStart = l.kernel.brkStart
  nonMain : l.isMain = false →
    l'.kernel.brk = l.kernel.brk ∧ l'.shared.mm.mp.sbrkBase = l.shared.mm.mp.sbrkBase
  /-- A non-main body never lowers the kernel bytes not held by `mmap`ed chunks (it maps more, or
  unmaps only `mmap`ed chunks): the main arena's `LocalWF.sysMain` survives it. -/
  acct : l.isMain = false →
    l.kernel.total + l'.shared.mm.mp.mmappedMem ≤ l'.kernel.total + l.shared.mm.mp.mmappedMem
  init : l'.shared.init = l.shared.init
  arenas : l'.shared.arenas = l.shared.arenas ∧ l'.shared.freeList = l.shared.freeList ∧
    l'.shared.narenas = l.shared.narenas
  arena : l'.thread.arena = l.thread.arena
  heaps : l.av.heaps ≠ [] → l'.av.heaps ≠ []
  clients : ∀ c ∈ l.av.chunks, c.use = .client → (c.addr + C.hdr, usable C c false) ∉ freed →
    c ∈ l'.av.chunks
  fresh : ∀ tc' i e, l'.thread.tcache = some tc' → e ∈ tc'.bins i →
    (∃ tc j, l.thread.tcache = some tc ∧ e ∈ tc.bins j) ∨
    ((∃ c ∈ l'.av.chunks, c.addr = e.1 ∧ c.size = e.2 ∧ c.use = .client) ∧
      ((e.1 + C.hdr, e.2 - C.sizeSz) ∈ freed ∨ ∀ c ∈ l.av.chunks, c.addr = e.1 → c.use ≠ .client))

/-- **A tcache entry apart from the view (a chunk of another arena) stays** (every body but
`tcache_get`, which may hand out such a chunk). -/
def KeptAway (l l' : Local) : Prop :=
  ∀ tc i e, l.thread.tcache = some tc → e ∈ tc.bins i → Away l.spans e →
    ∃ tc', l'.thread.tcache = some tc' ∧ e ∈ tc'.bins i

/-! ## Body obligations for the world (wave 3)

`Task.algo.wfWorld` and `Task.algo.mallocTotal` follow from these (`Algo.wfWorld_of`,
`Algo.mallocTotal_of`): the bodies on a view with its spatial facts (`LocalSp`, which `WorldWF`
gives every view) keep `LocalWF`, change the live set as the call says, and have a `Frame`. -/

/-- **`Task.algo.bodyMalloc`**: `_int_malloc`, after `ptmalloc_init` (`__malloc_initialized`
set: every caller runs `ptmalloc_init` first; before it, `LocalWF.init` says there is no heap and
no `mmap`ed chunk, which a `sysmalloc` would break). -/
def Task.algo.bodyMalloc (C : Config) : Prop :=
  C.Ok → ∀ l l' n p, LocalWF C l → LocalSp C l → l.shared.init = true →
    intMalloc C l n = .ok (p, l') →
    MallocOK C n l p l' ∧ Frame C l l' [] ∧ KeptAway l l' ∧
      (l.thread.tcache = none → l'.thread.tcache = none)

/-- **`Task.algo.bodyFree`**: `_int_free` of a live payload of the arena. -/
def Task.algo.bodyFree (C : Config) : Prop :=
  C.Ok → ∀ l l' p u, LocalWF C l → LocalSp C l → (p, u) ∈ l.arenaLive C →
    intFree C l (p - C.hdr) = .ok l' →
    LocalWF C l' ∧ Frame C l l' [(p, u)] ∧ KeptAway l l' ∧
      (l'.live C).Perm ((l.live C).erase (p, u))

/-- **`Task.algo.totalMalloc`**: `_int_malloc` does not abort on a view with its spatial facts. -/
def Task.algo.totalMalloc (C : Config) : Prop :=
  C.Ok → ∀ l, LocalWF C l → LocalSp C l → ∀ n, ∃ r, intMalloc C l n = .ok r

/-- **`Task.algo.totalFree`**: `_int_free` of a live payload of the arena does not abort on a
view with its spatial facts (`LocalSp.heaps`: `heap_trim` needs the arena's heap). -/
def Task.algo.totalFree (C : Config) : Prop :=
  C.Ok → ∀ l, LocalWF C l → LocalSp C l → ∀ p u, (p, u) ∈ l.arenaLive C →
    ∃ l', intFree C l (p - C.hdr) = .ok l'

end Silmaril.Libc.Ptmalloc.Algo
