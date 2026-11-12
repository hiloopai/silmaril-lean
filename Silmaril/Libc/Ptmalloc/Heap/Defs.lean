module

public import Silmaril.Libc.Ptmalloc.Tcache.Defs
public import Silmaril.Libc.Ptmalloc.Fastbins.Defs
public import Silmaril.Libc.Ptmalloc.Bins.Defs
public import Silmaril.Libc.Ptmalloc.Unsorted.Defs
public import Silmaril.Libc.Ptmalloc.Top.Defs
public import Silmaril.Libc.Ptmalloc.Mmap.Defs
public import Silmaril.Libc.Ptmalloc.Kernel.Defs

/-!
# ptmalloc: the abstract heap, composed from component sub-models

The algorithm runs on a state **composed of component sub-models**, each with its own state,
invariant and operations (modules `Tcache`, `Fastbins`, `Bins`, `Unsorted`, `Top`, `Mmap`,
`Kernel`; the surroundings are `Env`), and **partitioned by owner**:

| part | type | owner | components |
|---|---|---|---|
| thread-local | `ThreadSt` | the thread | `Tcache`, `thread_arena`, `tcache_shutting_down`, `errno` |
| per-arena | `ArenaSt` | the arena's lock invariant | `Top` (tiling, top, `system_mem`), `Fastbins`, `Bins` (+ binmap), `Unsorted` (+ `last_remainder`) |
| shared | `SharedSt` | atomics / `list_lock` / init-once | `Mmap` (`mmap`ed chunks, `mp_`), `__malloc_initialized`, `tcache_key`, the arena list |
| kernel | `KernelSt` | the kernel | `Kernel` (break, maps, the answer oracle) |

**Composition.** `ArenaWF` is the conjunction of the component invariants, each applied to its
*view* of the tiling (`Chunk.view`), plus the link facts no single component states. So a path
proof touching only the fastbins proves `FastWF` for the new fastbins and the new fast view, and
gets the other components' invariants from "their view did not change"
(`Silmaril.Libc.Ptmalloc.Heap.Thms`: `ArenaWF.withFast`, …). `World.put` frames the other arenas
and threads by construction; `Local` is what one body sees (one arena, the calling thread, the
shared part, the kernel).

**Model fixes already in the shape** (found by an earlier, monolithic proof):
M2 (`MpSt.sbrkBase`), M3 (`Seg.endAddr`), W6 (`Seg.lastFree`), W15a/c, W16b, M7, M6 (arena list
and `attached`), W14/W15b/M5 (`MainBrk`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-! ## The parts -/

/-- **Thread-local state.** -/
structure ThreadSt where
  tcache : Option TcacheSt := none
  arena : Option Nat := none
  shuttingDown : Bool := false
  errno : Nat := 0

/-- **One arena** (`malloc_state`) and its heap, as components. -/
structure ArenaSt where
  tiles : TopSt
  fast : FastSt
  bins : BinsSt
  unsorted : UnsortedSt
  /-- `attached_threads`. -/
  attached : Nat := 1
  /-- A non-main arena's `heap_info` mappings (address, size), the current heap first. -/
  heaps : List (Nat × Nat) := []
  /-- **Ghost**: the bytes of the current heap's `HEAP_MAX_SIZE` reservation past its end
  (`HEAP_MAX_SIZE - size`; mapped `PROT_NONE`, what `grow_heap` makes usable). Not read by the
  algorithm; it makes the reservation the arena's own (`ArenaSt.heapSpans`). -/
  reserve : Nat := 0

/-- **Shared state.** -/
structure SharedSt where
  init : Bool
  key : Nat
  mm : MmapSt
  /-- The arena list after `main_arena`, `free_list`, `narenas` (M6). -/
  arenas : List Nat := []
  freeList : List Nat := []
  narenas : Nat := 1

/-- **The whole allocator state.** -/
structure World where
  mainArena : Nat
  arenas : Nat → Option ArenaSt
  tids : List Nat
  threads : Nat → ThreadSt
  shared : SharedSt
  kernel : KernelSt

/-- **What one body sees.** -/
structure Local where
  avAddr : Nat
  isMain : Bool
  av : ArenaSt
  thread : ThreadSt
  shared : SharedSt
  kernel : KernelSt

/-- `SINGLE_THREAD_P`: the process has (at most) one thread. -/
def World.single (w : World) : Bool := decide (w.tids.length ≤ 1)

/-- The body's view of thread `tid` at arena `a`. -/
def World.local? (w : World) (tid a : Nat) : Option Local :=
  (w.arenas a).map fun av =>
    { avAddr := a, isMain := decide (a = w.mainArena), av, thread := w.threads tid,
      shared := w.shared, kernel := w.kernel }

/-- Put a body's result back. -/
def World.put (w : World) (tid : Nat) (l : Local) : World :=
  { w with
    arenas := fun a => if a = l.avAddr then some l.av else w.arenas a
    threads := fun t => if t = tid then l.thread else w.threads t
    shared := l.shared, kernel := l.kernel }

/-! ## Views and live payloads -/

namespace ArenaSt

variable (av : ArenaSt)

/-- The arena's chunks. -/
def chunks : List Chunk := av.tiles.heapChunks

/-- The views of the components. -/
def fastView : List Chunk := Chunk.view Use.isFast av.chunks
def sortedView : List Chunk := Chunk.view Use.isSorted av.chunks
def unsortedView : List Chunk := Chunk.view Use.isUnsorted av.chunks

/-- **The payloads lent out of the arena** (`client` chunks: live or parked in a tcache). -/
def out (C : Config) : List (Nat × Nat) :=
  (Chunk.view (· = .client) av.chunks).map fun c => (c.addr + C.hdr, usable C c false)

end ArenaSt

/-- The live `mmap`ed payloads. -/
def SharedSt.live (C : Config) (sh : SharedSt) : List (Nat × Nat) :=
  (sh.mm.chunks.filter (·.use = .client)).map fun c => (c.addr + C.hdr, usable C c true)

/-- The payloads parked in a thread's tcache. -/
def ThreadSt.parked (C : Config) (t : ThreadSt) : List (Nat × Nat) :=
  (t.tcache.map (·.payloads C)).getD []

/-- The arenas, `main_arena` first. -/
def World.arenaAddrs (w : World) : List Nat := w.mainArena :: w.shared.arenas

/-- Every chunk of every arena. -/
def World.chunks (w : World) : List Chunk :=
  w.arenaAddrs.flatMap fun a => ((w.arenas a).map (·.chunks)).getD []

/-- **The live payloads of the world** (the institution's live set). -/
def World.live (C : Config) (w : World) : List (Nat × Nat) :=
  let parked := w.tids.flatMap fun t => (w.threads t).parked C
  ((w.arenaAddrs.flatMap fun a => ((w.arenas a).map (·.out C)).getD []).filter
      fun pu => !parked.contains pu) ++ w.shared.live C

/-- **The live payloads of the body's arena** (lent out, not parked in this thread's tcache): the
payloads `_int_free` can receive (`__libc_free` sends `mmap`ed chunks to `munmap_chunk`). -/
def Local.arenaLive (C : Config) (l : Local) : List (Nat × Nat) :=
  (l.av.out C).filter (fun pu => !(l.thread.parked C).contains pu)

/-- **The live payloads one body accounts for** (`= l.arenaLive C ++ l.shared.live C`). -/
def Local.live (C : Config) (l : Local) : List (Nat × Nat) :=
  (l.av.out C).filter (fun pu => !(l.thread.parked C).contains pu) ++ l.shared.live C

/-! ## Invariants: components composed -/

/-- **An arena is well formed**: each component on its view, plus the links. -/
structure ArenaWF (C : Config) (av : ArenaSt) : Prop where
  tiles : TopWF C av.tiles
  fast : FastWF C av.fast av.fastView
  bins : BinsWF C av.bins av.sortedView av.tiles.sizeAt
  unsorted : UnsortedWF C av.unsorted av.unsortedView
  /-- Link: no arena chunk is `internal` except a tcache struct (`tcache_init`'s allocation). -/
  internal : ∀ c ∈ av.chunks, c.use = .internal → C.minSize ≤ c.size

/-- **The main arena and `mp_` agree** (W17/M2). -/
def MainSbrk (sh : SharedSt) (av : ArenaSt) : Prop :=
  (sh.mm.mp.sbrkBase = 0 ↔ av.tiles.start = 0) ∧
    (av.tiles.noncontig = false → sh.mm.mp.sbrkBase = av.tiles.start ∧ av.tiles.old = [])

/-- **The kernel and the main arena agree** (W14, W15b, W15d, M5). -/
def MainBrk (C : Config) (k : KernelSt) (av : ArenaSt) : Prop :=
  C.page ≤ k.brkStart ∧ k.brkStart ≤ k.brk ∧ k.brk % C.page = 0 ∧
  (av.tiles.start ≠ 0 → (av.tiles.top + av.tiles.topSize) % C.page = 0 ∧
    (av.tiles.noncontig = false → k.brkStart ≤ av.tiles.start ∧
      k.brk = av.tiles.top + av.tiles.topSize))

/-- **The shared part is well formed.** -/
structure SharedWF (C : Config) (sh : SharedSt) : Prop where
  mm : MmapWF C sh.mm
  narenas : sh.narenas = sh.arenas.length + 1
  freeListSub : ∀ a ∈ sh.freeList, a ∈ sh.arenas

/-- The byte ranges a non-main arena owns besides its chunks and top: the first byte of every
heap (its `heap_info`, never a chunk), and the current heap's reservation past its end (what
`grow_heap` hands to top; `ArenaSt.reserve`). With them in the spans, `Apart` says no other
arena's or `mmap`ed range lies in a heap's reservation, and heap addresses are distinct. -/
def ArenaSt.heapSpans (av : ArenaSt) : List (Nat × Nat) :=
  av.heaps.map (fun hp => (hp.1, 1)) ++
    (match av.heaps with
     | (h, hs) :: _ => if av.reserve = 0 then [] else [(h + hs, av.reserve)]
     | [] => [])

/-- The byte ranges an arena owns: its chunks and, once it has a heap, its top chunk; and its
heaps' (`heapSpans`). -/
def ArenaSt.spans (av : ArenaSt) : List (Nat × Nat) := av.tiles.spans ++ av.heapSpans

/-- The byte ranges one body sees: its arena's and the `mmap`ed chunks. -/
def Local.spans (l : Local) : List (Nat × Nat) :=
  l.av.spans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size))

/-- **A non-main arena's heaps** (glibc: `heap_for_ptr (top)` is the current heap, `grow_heap`
extends it inside its `HEAP_MAX_SIZE` reservation, `system_mem` is the sum of the heap sizes):
* `cur`: the current heap `(h, hs)` holds the top chunk, which ends the heap
  (`top + topSize = h + hs`), after its `heap_info` (`h < start`); its size and the ghost
  reservation make `HEAP_MAX_SIZE`;
* `addrs`: every heap is a `HEAP_MAX_SIZE`-aligned reservation in the user address space;
* `sysMem`: `system_mem` is at most the sum of the heap sizes (so, with the distinct heap
  addresses, below `2 ^ 47`). -/
structure HeapWF (C : Config) (av : ArenaSt) : Prop where
  cur : ∃ h hs rest, av.heaps = (h, hs) :: rest ∧ h < av.tiles.start ∧
    av.tiles.top + av.tiles.topSize = h + hs ∧ hs + av.reserve = C.heapMaxSize
  addrs : ∀ hp ∈ av.heaps, hp.1 % C.heapMaxSize = 0 ∧ hp.1 + C.heapMaxSize ≤ KernelSt.userTop ∧
    hp.2 ≤ C.heapMaxSize
  sysMem : av.tiles.systemMem ≤ (av.heaps.map (·.2)).sum

/-- **One body's view is well formed.** -/
structure LocalWF (C : Config) (l : Local) : Prop where
  arena : ArenaWF C l.av
  shared : SharedWF C l.shared
  tcache : ∀ tc, l.thread.tcache = some tc → TcacheWF C tc
  main : l.isMain = true → MainSbrk l.shared l.av ∧ MainBrk C l.kernel l.av
  init : l.shared.init = false → l.av.tiles.start = 0 ∧ l.shared.mm.chunks = [] ∧ l.thread.tcache = none
  /-- **Spatial separation** (what `malloc`'s fresh payload being apart from every live one rests
  on): the arena's chunks and top and the `mmap`ed chunks are non-empty and pairwise apart. -/
  apart : Apart l.spans
  /-- `mmap`ed chunks hold more than a header and lie below `2 ^ 64`. -/
  mmSize : ∀ c ∈ l.shared.mm.chunks, C.hdr < c.size ∧ c.addr + c.size ≤ 2 ^ 64
  /-- A non-main arena's heaps (`HeapWF`). -/
  heap : l.isMain = false → HeapWF C l.av
  /-- **The main arena's `system_mem` is kernel memory** (wave 5): the main arena's bytes and the
  `mmap`ed chunks' are bytes the process has from the kernel, so `system_mem` stays below
  `userTop` (`TopWF.sysMemBound` survives `sysmalloc`'s growth). A non-main body never lowers
  `total − mmapped_mem` (`Frame.acct`), so the clause is local to the main view. -/
  sysMain : l.isMain = true → l.av.tiles.systemMem + l.shared.mm.mp.mmappedMem ≤ l.kernel.total

/-- The byte ranges the allocator owns: every arena's, then the `mmap`ed chunks. -/
def World.spans (w : World) : List (Nat × Nat) :=
  (w.arenaAddrs.flatMap fun a => ((w.arenas a).map (·.spans)).getD []) ++
    w.shared.mm.chunks.map (fun c => (c.addr, c.size))

/-- **The world is well formed.** -/
structure WorldWF (C : Config) (w : World) : Prop where
  main : (w.arenas w.mainArena).isSome
  arenas : ∀ a, a ∈ w.arenaAddrs ↔ (w.arenas a).isSome
  arenaWF : ∀ a av, w.arenas a = some av → ArenaWF C av
  shared : SharedWF C w.shared
  /-- Every thread's view of every arena is well formed (`free` runs `_int_free` on the chunk's
  arena, whatever the thread's `thread_arena`). -/
  locals : ∀ tid a l, tid ∈ w.tids → w.local? tid a = some l → LocalWF C l
  /-- The arena list has no duplicate (`main_arena` is not in `shared.arenas`). -/
  arenaNodup : w.arenaAddrs.Nodup
  /-- **Spatial separation**: the chunks and tops of all arenas and the `mmap`ed chunks are
  pairwise apart (glibc: they live in disjoint kernel mappings / the break area). -/
  apart : Apart w.spans
  /-- `mmap`ed chunks hold more than a header and lie below `2 ^ 64`. -/
  mmSize : ∀ c ∈ w.shared.mm.chunks, C.hdr < c.size ∧ c.addr + c.size ≤ 2 ^ 64
  parked : ∀ tid tc, tid ∈ w.tids → (w.threads tid).tcache = some tc → ∀ i c, c ∈ tc.bins i →
    ∃ d ∈ w.chunks, d.addr = c.1 ∧ d.size = c.2 ∧ d.use = .client
  parkedOnce : (w.tids.flatMap fun t => (w.threads t).parked C).Nodup
  tidsNodup : w.tids.Nodup
  /-- Every thread's `thread_arena` is an arena (`malloc` runs its tcache path on it). -/
  threadArena : ∀ t a, t ∈ w.tids → (w.threads t).arena = some a → a ∈ w.arenaAddrs
  /-- **Kernel link**: every span is the process's memory (the break area or a mapping), so a
  fresh `sbrk`/`mmap` range is apart from it. -/
  covered : ∀ r ∈ w.spans, w.kernel.Covers r
  /-- The arena structs: each arena's first byte is the process's memory (main_arena's in libc's
  data, a non-main arena's in its heap's mapping) and apart from every span, so `_int_new_arena`
  never lands on an existing arena. -/
  structs : ∀ a ∈ w.arenaAddrs, w.kernel.Has a ∧ Away w.spans (a, 1)
  /-- A non-main arena has a heap (`heap_trim` and `sysmalloc` read `heap_for_ptr (top)`). -/
  heaps : ∀ a av, w.arenas a = some av → a ≠ w.mainArena → av.heaps ≠ []

/-- **The spatial facts of one body's view** that `WorldWF` gives every view (`Algo.localSp`):
its spans are the process's memory; each tcache entry is a client chunk of the arena (of that
size) or apart from the view's spans and the process's memory (a chunk of another arena); a
non-main arena has a heap. -/
structure LocalSp (C : Config) (l : Local) : Prop where
  covered : ∀ r ∈ l.spans, l.kernel.Covers r
  entries : ∀ tc, l.thread.tcache = some tc → ∀ i e, e ∈ tc.bins i →
    (∃ c ∈ l.av.chunks, c.addr = e.1 ∧ c.size = e.2 ∧ c.use = .client) ∨
      (Away l.spans e ∧ l.kernel.Covers e)
  heaps : l.isMain = false → l.av.heaps ≠ []

end Silmaril.Libc.Ptmalloc
