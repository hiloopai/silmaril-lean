module

public import Silmaril.Libc.Ptmalloc.Heap.Defs
public import Silmaril.Libc.Ptmalloc.Layout.Defs
public import Silmaril.Data.SepList.Defs
public import Silmaril.Data.Bitmap.Defs
public import Silmaril.Data.BoundaryTag.Defs

/-!
# ptmalloc: the representation (abstract heap ↔ bytes)

The representation is a **function** from the abstract state to the cells it must find in
memory, one fragment per component, built from the generic data-structure library
(`Silmaril.Data.SepList`: `dll`, `slist`, `skip`; `Silmaril.Data.Bitmap`; `Silmaril.Data.BoundaryTag`:
header runs) instantiated with glibc's link layouts and encoding (`PROTECT_PTR` from `Config`).
So it is

* **decidable** on a concrete memory (`Frag.Holds`, `MemView.Backs`), as `difftest` needs;
* **footprint-explicit** (`Frag.bytes`), with the frame rule `Silmaril.Data.Frag.holds_frame`;
* **compositional**: `LocalRep` is the conjunction of the components' fragments, pairwise
  disjoint, so a path that touches one component re-proves one fragment.

Parametric in `C : Config`, the struct offsets `L : Layout` and the relocated addresses
(`Statics`, `TlsAddrs`); no ISA type (`MemView` is abstract; the x86 layer instantiates it).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

open Silmaril.Data
open Silmaril.Data.SepList (Links SLinks dll slist skip)

/-- **The relocated statics** the representation needs. -/
structure Statics where
  mp : Nat
  mallocInitialized : Nat
  tcacheKey : Nat
  globalMaxFast : Nat
  perturbByte : Nat
  freeList : Nat
  narenas : Nat
  /-- Width in bytes of `global_max_fast` (D2/V1-F1: `uint8_t` in 2.39/2.40, `INTERNAL_SIZE_T`
  = 8 in 2.36); from `Syms.globalMaxFastWidth`. -/
  globalMaxFastWidth : Nat := 8
  deriving DecidableEq, Repr

/-- The calling thread's TLS variables (absolute addresses). -/
structure TlsAddrs where
  tcache : Nat
  arena : Nat
  shutdown : Nat
  errno : Nat
  deriving DecidableEq, Repr

/-- A word cell. -/
def Cell.w (a v : Nat) : Cell := ⟨a, 8, v⟩

section
variable (C : Config) (L : Layout)

/-! ## glibc's instances of the generic predicates -/

/-- `fd`/`bk` of a chunk (`SIZE_SZ = 8`). -/
def binLinks : Links := { fd := 16, bk := 24 }
/-- `fd_nextsize`/`bk_nextsize`. -/
def nsLinks : Links := { fd := 32, bk := 40 }
/-- A fastbin's link (at `fd`, safe-linked). -/
def fastLinks : SLinks := { link := 16, enc := C.protect }
/-- A tcache entry's link (`next`, at the payload, safe-linked). -/
def tcLinks : SLinks := { link := 0, enc := C.protect }
/-- Chunk headers: `size` at offset 8, `PREV_INUSE`, boundary tag = next chunk's `prev_size`. -/
def chunkTag : Silmaril.Data.BoundaryTag.Tag := { sizeOff := 8 }

/-- A chunk as a boundary-tag block. -/
def Chunk.blk (c : Chunk) : Silmaril.Data.BoundaryTag.Blk := ⟨c.addr, c.size, c.use.tagFree⟩

/-- The sentinel of bin `i` of the arena at `avAddr` (`bin_at`). -/
def binAt (avAddr i : Nat) : Nat := avAddr + L.arBins + 16 * (i - 1) - 16

/-! ## One fragment per component -/

/-- **`Fastbins`**: the heads in `malloc_state`, the safe-linked lists, `have_fastchunks`. -/
def fastFrag (avAddr : Nat) (fs : FastSt) : Frag :=
  ⟨avAddr + L.arHaveFast, 4, if fs.haveFast then 1 else 0⟩ ::
  (List.range C.nFast).flatMap fun i =>
    Cell.w (avAddr + L.arFastbins + 8 * i) ((fs.lists i).headD 0) :: slist (fastLinks C) (fs.lists i)

/-- **`Bins`**: every small/large bin `2 … nBins - 1` as a `dll` with its sentinel (bin 127, never
used, self-linked: W17/M1), the large bins' skip lists, the binmap. -/
def binsFrag (avAddr : Nat) (bs : BinsSt) (sz : Nat → Nat) : Frag :=
  ((List.range (C.nBins - 2)).flatMap fun k =>
    let i := k + 2
    dll binLinks (binAt L avAddr i) (bs.lists i) ++
      (if C.nSmallBins ≤ i then skip nsLinks sz (bs.lists i) else [])) ++
  Silmaril.Data.Bitmap.frag (avAddr + L.arBinmap) 4 4 bs.binmap

/-- **`Unsorted`**: bin 1 as a `dll`, null skip links on its large chunks, `last_remainder`. -/
def unsortedFrag (avAddr : Nat) (us : UnsortedSt) (sz : Nat → Nat) : Frag :=
  Cell.w (avAddr + L.arLastRem) us.lastRem :: dll binLinks (binAt L avAddr 1) us.list ++
  (us.list.filter fun a => C.minLargeSize ≤ sz a).flatMap fun a => [Cell.w (a + 32) 0, Cell.w (a + 40) 0]

/-- **`Top`**: the header runs of every segment (`BoundaryTag.run`), the closed segments' fence
posts (W6), the top chunk's header and `top`, `system_mem`, `max_system_mem`, the flags. -/
def tilesFrag (avAddr : Nat) (ts : TopSt) : Frag :=
  [⟨avAddr + L.arFlags, 4, if ts.noncontig then 2 else 0⟩,
   Cell.w (avAddr + L.arTop) (if ts.start = 0 then binAt L avAddr 1 else ts.top),
   Cell.w (avAddr + L.arSystemMem) ts.systemMem, Cell.w (avAddr + L.arMaxSystemMem) ts.maxSystemMem] ++
  (ts.old.flatMap fun g =>
    Silmaril.Data.BoundaryTag.run chunkTag false ((layout g.start g.chunks).map Chunk.blk) ++
      [Cell.w (g.endAddr + 8) (C.hdr + if g.lastFree then 0 else Config.prevInuse),
       Cell.w (g.endAddr + C.hdr + 8) (C.hdr + Config.prevInuse)]) ++
  Silmaril.Data.BoundaryTag.run chunkTag false ((layout ts.start ts.chunks).map Chunk.blk) ++
  (if ts.start = 0 then [] else [Cell.w (ts.top + 8) (ts.topSize + Config.prevInuse)])

/-- **One arena's fragment**: the mutex (free between calls), `attached_threads`, and the
components'. (`next`/`next_free` are the shared arena list's, M6: not here.) -/
def arenaFrag (avAddr : Nat) (av : ArenaSt) : Frag :=
  [⟨avAddr + L.arMutex, 4, 0⟩, Cell.w (avAddr + L.arAttached) av.attached] ++
  tilesFrag C L avAddr av.tiles ++ fastFrag C L avAddr av.fast ++
  binsFrag C L avAddr av.bins av.tiles.sizeAt ++ unsortedFrag C L avAddr av.unsorted av.tiles.sizeAt

/-- **The uninitialised image of an arena** (D1): before `ptmalloc_init` runs
`malloc_init_state`, the static `main_arena` is zero except `attached_threads` (1) and `next`
(the arena list's, M6: not here). The bins are **not** self-linked and `top` is 0, so the image
is not `arenaFrag` of an empty arena. The cells carry the abstract values where glibc's word is
a plain copy of one (`top`, `last_remainder`, the fastbin heads, the binmap, the counters), so a
zero image forces them to their load-time values (`Algo.initWorld`); the bin words are 0.
`malloc_init_state` then writes the `arenaFrag` image (`dll binLinks (binAt i) []`, `top =
bin_at (1)`). -/
def arenaFragPre (avAddr : Nat) (av : ArenaSt) : Frag :=
  [⟨avAddr + L.arMutex, 4, 0⟩, Cell.w (avAddr + L.arAttached) av.attached,
   ⟨avAddr + L.arFlags, 4, if av.tiles.noncontig then 2 else 0⟩,
   ⟨avAddr + L.arHaveFast, 4, if av.fast.haveFast then 1 else 0⟩,
   Cell.w (avAddr + L.arTop) av.tiles.top, Cell.w (avAddr + L.arLastRem) av.unsorted.lastRem,
   Cell.w (avAddr + L.arSystemMem) av.tiles.systemMem,
   Cell.w (avAddr + L.arMaxSystemMem) av.tiles.maxSystemMem] ++
  (List.range C.nFast).map (fun i => Cell.w (avAddr + L.arFastbins + 8 * i) ((av.fast.lists i).headD 0)) ++
  (List.range (2 * (C.nBins - 1))).map (fun k => Cell.w (avAddr + L.arBins + 8 * k) 0) ++
  Silmaril.Data.Bitmap.frag (avAddr + L.arBinmap) 4 4 av.bins.binmap

/-- **An arena's fragment, initialised or not** (D1): `__malloc_initialized` selects the
`malloc_init_state` image (`arenaFrag`) or the static one (`arenaFragPre`). Only `main_arena`
exists before initialisation; every other arena is created initialised. -/
def arenaRep (init : Bool) (avAddr : Nat) (av : ArenaSt) : Frag :=
  if init then arenaFrag C L avAddr av else arenaFragPre C L avAddr av

/-- **`Tcache`**: counts, heads, each bin's safe-linked list at the payloads, the key in each
parked chunk. -/
def tcacheFrag (key : Nat) (tc : TcacheSt) : Frag :=
  (List.range C.tcacheBins).flatMap fun i =>
    let ps := (tc.bins i).map fun c => c.1 + C.hdr
    ⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length⟩ ::
      Cell.w (tc.addr + L.tcEntries + 8 * i) (ps.headD 0) ::
      (slist (tcLinks C) ps ++ ps.map fun p => Cell.w (p + 8) key)

/-- **One thread's fragment**: its TLS variables and its tcache. -/
def threadFrag (T : TlsAddrs) (avAddr key : Nat) (init : Bool) (t : ThreadSt) : Frag :=
  [Cell.w T.tcache ((t.tcache.map (·.addr)).getD 0),
   Cell.w T.arena (if init then t.arena.getD avAddr else 0),
   ⟨T.shutdown, 1, if t.shuttingDown then 1 else 0⟩] ++
  ((t.tcache.map (tcacheFrag C L key)).getD [])

/-- **`Mmap`** and the shared words: `__malloc_initialized` (a 1-byte `bool`, D3), `tcache_key`, `mp_`'s changing words
(`sbrk_base` its own, W17/M2), `global_max_fast` (`St.globalMaxFastWidth` bytes, D2), `perturb_byte`, the `mmap`ed client chunks'
`prev_size = 0` and `size | IS_MMAPPED`. -/
def sharedFrag (St : Statics) (sh : SharedSt) : Frag :=
  let f := fun o => St.mp + o
  let mp := sh.mm.mp
  [⟨St.mallocInitialized, 1, if sh.init then 1 else 0⟩, Cell.w St.tcacheKey sh.key,
   Cell.w (f L.mpTrim) mp.trimThreshold, Cell.w (f L.mpMmapThreshold) mp.mmapThreshold,
   ⟨f L.mpNMmaps, 4, mp.nMmaps⟩, ⟨f L.mpMaxNMmaps, 4, mp.maxNMmaps⟩,
   Cell.w (f L.mpMmappedMem) mp.mmappedMem, Cell.w (f L.mpMaxMmappedMem) mp.maxMmappedMem,
   Cell.w (f L.mpSbrkBase) mp.sbrkBase, ⟨f L.mpNoDyn, 4, if mp.noDyn then 1 else 0⟩,
   ⟨St.globalMaxFast, St.globalMaxFastWidth, if sh.init then C.maxFast else 0⟩, ⟨St.perturbByte, 4, 0⟩] ++
  ((sh.mm.chunks.filter (·.use = .client)).flatMap fun c =>
    [Cell.w c.addr 0, Cell.w (c.addr + 8) (c.size + Config.isMmapped)])

/-- **The bytes a heap owns beyond its cells** (W3, W17/M9): every chunk's extent and the top
chunk must be mapped, writable and backed. -/
def spansOf (av : ArenaSt) : List (Nat × Nat) :=
  (av.chunks.map fun c => (c.addr, c.size + 8)) ++
    (if av.tiles.start = 0 then [] else [(av.tiles.top, max av.tiles.topSize 16)])

/-- **The representation of one body's view**: the arena's (initialised or not, D1), the
thread's and the shared fragments hold, pairwise disjoint, and the heap's spans are backed. -/
def LocalRep (St : Statics) (T : TlsAddrs) (l : Local) (v : MemView) : Prop :=
  let fa := arenaRep C L l.shared.init l.avAddr l.av
  let ft := threadFrag C L T l.avAddr l.shared.key l.shared.init l.thread
  let fs := sharedFrag C L St l.shared
  fa.Holds v ∧ ft.Holds v ∧ fs.Holds v ∧ v.Backs (spansOf l.av) ∧
    (fa ++ ft ++ fs).bytes.Nodup

instance (St : Statics) (T : TlsAddrs) (l : Local) (v : MemView) :
    Decidable (LocalRep C L St T l v) := by
  unfold LocalRep; exact inferInstance

/-- **Executable `LocalRep` check** for memory dumps: the cell checks, the backing check and the
`O(n log n)` separation check `Frag.sepB` (the `Decidable` instance's `Nodup` is quadratic).
Sound: `Silmaril.Libc.Ptmalloc.Seplist.localRep_of_check`. -/
def LocalRep.check (St : Statics) (T : TlsAddrs) (l : Local) (v : MemView) : Bool :=
  let fa := arenaRep C L l.shared.init l.avAddr l.av
  let ft := threadFrag C L T l.avAddr l.shared.key l.shared.init l.thread
  let fs := sharedFrag C L St l.shared
  decide (fa.Holds v) && decide (ft.Holds v) && decide (fs.Holds v) &&
    decide (v.Backs (spansOf l.av)) && Frag.sepB (fa ++ ft ++ fs)

end

/-! ## Obligations (owned by `seplist`) -/

/-- **`Task.seplist.localFrame`**: a body that changes only the thread part (the tcache paths)
re-establishes `LocalRep` from the new thread fragment alone (instance of `Frag.holds_frame`).
The template every block-simulation frame obligation reduces to. -/
def Task.seplist.localFrame : Prop :=
  ∀ (C : Config) (L : Layout) (St : Statics) (T : TlsAddrs) (l l' : Local) (v v' : MemView),
    LocalRep C L St T l v → l'.avAddr = l.avAddr → l'.av = l.av → l'.shared = l.shared →
    v.AgreeOn v' ((arenaRep C L l.shared.init l.avAddr l.av) ++ sharedFrag C L St l.shared).bytes →
    v'.Backs (spansOf l.av) →
    let ft' := threadFrag C L T l.avAddr l.shared.key l.shared.init l'.thread
    ft'.Holds v' →
    (arenaRep C L l.shared.init l.avAddr l.av ++ ft' ++ sharedFrag C L St l.shared).bytes.Nodup →
    LocalRep C L St T l' v'

/-- **`Task.seplist.leafTcacheGet`**: each leaf operation's fragment change is a listed set of
stores (the instance of the generic `dll`/`slist`/`run` lemmas for glibc). Here `tcache_get`:
the count, the head, and the popped entry's `key` (cleared). Revised by `seplist`: assumes the
fragment is separated, the count width is positive and fits `tcacheCount`, and the payload
addresses fit a word. -/
def Task.seplist.leafTcacheGet : Prop :=
  ∀ (C : Config) (L : Layout) (key : Nat) (tc tc' : TcacheSt) (i p : Nat) (v : MemView),
    C.Ok → TcacheWF C tc → i < C.tcacheBins → tc.get C i = some (p, tc') →
    0 < C.tcacheCountWidth → C.tcacheCount < 256 ^ C.tcacheCountWidth →
    (∀ c ∈ tc.bins i, c.1 + C.hdr < 256 ^ 8) →
    (tcacheFrag C L key tc).Holds v → (tcacheFrag C L key tc).Sep →
    (tcacheFrag C L key tc').Holds (v.storeAll
      [⟨tc.addr + L.tcCounts + C.tcacheCountWidth * i, C.tcacheCountWidth, (tc.bins i).length - 1⟩,
       Cell.w (tc.addr + L.tcEntries + 8 * i) (((tc'.bins i).map (·.1 + C.hdr)).headD 0),
       Cell.w (p + 8) 0])

end Silmaril.Libc.Ptmalloc
