module

public import Silmaril.Libc.Ptmalloc.Chunk.Defs

/-!
# ptmalloc component: `mmap`ed chunks and `mp_` (shared)

State `MmapSt`: the `mmap`ed chunks (no arena) and `mp_`'s changing fields (thresholds, counters,
`sbrk_base` as its own word: W17/M2). Invariant `MmapWF` (W16b bounds, M7 threshold floors,
whole-page client mappings). Operations `add`/`remove` (with the counters) and the dynamic
threshold update of `free` (`raise`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- **`mp_`'s changing fields.** -/
structure MpSt where
  trimThreshold : Nat
  mmapThreshold : Nat
  nMmaps : Nat := 0
  maxNMmaps : Nat := 0
  mmappedMem : Nat := 0
  maxMmappedMem : Nat := 0
  sbrkBase : Nat := 0
  noDyn : Bool := false

/-- **The `mmap`ed chunks and `mp_`.** -/
structure MmapSt where
  chunks : List Chunk := []
  mp : MpSt

namespace MmapSt

variable (ms : MmapSt)

/-- Record a new `mmap`ed chunk (`sysmalloc_mmap`'s accounting). -/
def add (c : Chunk) : MmapSt :=
  let n := ms.mp.nMmaps + 1
  let sz := ms.mp.mmappedMem + c.size
  let mp' : MpSt :=
    { ms.mp with
      nMmaps := n
      maxNMmaps := max n ms.mp.maxNMmaps
      mmappedMem := sz
      maxMmappedMem := max sz ms.mp.maxMmappedMem }
  { chunks := c :: ms.chunks, mp := mp' }

/-- Forget an unmapped chunk (`munmap_chunk`'s accounting). -/
def remove (c : Chunk) : MmapSt :=
  { chunks := ms.chunks.erase c,
    mp := { ms.mp with nMmaps := ms.mp.nMmaps - 1, mmappedMem := ms.mp.mmappedMem - c.size } }

/-- `free`'s dynamic threshold: freeing an `mmap`ed chunk of size `sz` whose raw size word
(`chunksize_nomask`, `sz + IS_MMAPPED`) is above `mmap_threshold` and at most
`DEFAULT_MMAP_THRESHOLD_MAX` raises `mmap_threshold` to `sz` and `trim_threshold` to `2 * sz`
(unless `no_dyn_threshold`). -/
def raise (C : Config) (sz : Nat) : MmapSt :=
  if ms.mp.noDyn = false ∧ ms.mp.mmapThreshold < sz + Config.isMmapped ∧
      sz + Config.isMmapped ≤ C.mmapThresholdMax then
    { ms with mp := { ms.mp with mmapThreshold := sz, trimThreshold := 2 * sz } }
  else ms

end MmapSt

/-- **The invariant of the `mmap`ed chunks and `mp_`.** -/
structure MmapWF (C : Config) (ms : MmapSt) : Prop where
  mpBound : ms.mp.trimThreshold < 2 ^ 64 ∧ ms.mp.mmapThreshold < 2 ^ 64 ∧
    ms.mp.mmappedMem < 2 ^ 64 ∧ ms.mp.maxMmappedMem < 2 ^ 64
  trimMin : C.trimThreshold ≤ ms.mp.trimThreshold ∧ C.mmapThreshold ≤ ms.mp.mmapThreshold
  use : ∀ c ∈ ms.chunks, c.use = .client ∨ c.use = .internal
  page : ∀ c ∈ ms.chunks, c.use = .client → c.addr % C.page = 0 ∧ c.size % C.page = 0
  nonNull : ∀ c ∈ ms.chunks, c.addr ≠ 0
  nodup : ms.chunks.Nodup
  /-- `mp_.mmapped_mem` is the total size of the `mmap`ed chunks (`sysmalloc_mmap` adds the
  mapping's size, `munmap_chunk` and `mremap_chunk` take it off). Without it `mpBound` does not
  survive a `sysmalloc_mmap`: a word-sized `mmapped_mem` near `2 ^ 64` would overflow. -/
  mem : ms.mp.mmappedMem = (ms.chunks.map (·.size)).sum

end Silmaril.Libc.Ptmalloc
