module

/-!
# ptmalloc: the per-version algorithm configuration

`Config` collects every **algorithm-level** constant in which glibc versions differ (or could
differ): the tcache geometry, the fastbin limit, the thresholds, `MINSIZE` and the alignment,
safe-linking, the tcache key's kind, the bin count and the bin-index function. Everything in
`Silmaril.Libc.Ptmalloc.{Heap,Algo,Rep,Env,Sim}` is parametric in a `C : Config` that satisfies
`Config.Ok`; the per-pin values live in `Silmaril.Libc.Ptmalloc.Version` (one record per pinned
libc). Byte offsets of glibc's structures are **not** here: they belong to the representation
layer (`Silmaril.Libc.Ptmalloc.Rep.Layout`), since the algorithm never sees them.

The helper functions mirror glibc's macros (`request2size`, `csize2tidx`, `fastbin_index`,
`smallbin_index`, `largebin_index_64`, `PROTECT_PTR`), with every constant taken from `C`.

## Variants

This module is the root of the layered ptmalloc development. A monolithic proof would fix
glibc 2.39's constants as top-level `def`s and state one `heapRep` over x86 memory. Here the
constants are a record, so a theorem proved once for `∀ C, C.Ok → …` instantiates for each version; the cost is
an extra argument everywhere and the `Ok` side conditions (decidable, discharged by `decide`
per version).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- What `tcache_key` is in this version: a pointer to the thread's tcache (2.29–2.33) or a
random word chosen once per process (2.34+, `tcache_key_initialize`). -/
inductive KeyKind where
  | tcachePtr
  | random
  deriving DecidableEq, Repr

/-- **Algorithm-level differences between glibc versions** that are not constants: each flag
switches one source-level behaviour of `malloc.c` that differs between the pinned versions
(source diff of glibc 2.36, 2.39 and 2.40 `malloc/malloc.c`, `malloc/arena.c` and the
distribution patches; the table is in `Silmaril.Libc.Ptmalloc.Version.V236`). Defaults are glibc
2.39/2.40, whose `malloc.c`/`arena.c` are identical. The algorithm model reads them where the
behaviours differ, so one theorem `∀ C, C.Ok → …` covers every pinned version. -/
structure Quirks where
  /-- 2.36 only: `_int_malloc`'s unsorted scan checks `bck->fd == victim` before it takes a
  chunk off the unsorted list ("malloc(): corrupted unsorted chunks 3"). -/
  unsortedTakeCheck : Bool := false
  /-- 2.39/2.40 only: `__libc_realloc` returns the old pointer when the request fits the
  chunk's usable size with less than `2 * SIZE_SZ` slack (mmapped: at most a page). -/
  reallocUsableFit : Bool := true
  /-- 2.39/2.40 only: `_int_realloc` also aborts when `oldsize ≠ chunksize (oldp)`
  ("realloc(): invalid old size"). -/
  reallocOldSizeCheck : Bool := true
  /-- 2.36 only: `sysmalloc` calls `sysmalloc_mmap_fallback` with `minsize` and `pagesize`
  transposed, so the fallback mapping is rounded up to `MMAP_AS_MORECORE_SIZE` (1 MiB) with a
  page as its minimum; 2.39/2.40 round to a page with a 1 MiB minimum. -/
  fallbackArgsSwapped : Bool := false
  /-- 2.39/2.40 only: `_mid_memalign` serves aligned requests from the tcache (`tcache_get_n`
  from the middle of a bin), and `_int_memalign` gives back a tail shorter than `MINSIZE` when
  the next chunk is free. (`memalign` is not an `Ops` entry yet; kept for the version table.) -/
  memalignTcache : Bool := true
  /-- 2.36 only: a new non-main heap is mapped with `MAP_NORESERVE` (a kernel-call argument). -/
  heapNoReserve : Bool := false
  deriving DecidableEq, Repr

/-- **The algorithm configuration of one glibc version** (x86-64 builds: `SIZE_SZ = 8`). -/
structure Config where
  /-- `SIZE_SZ`. -/
  sizeSz : Nat := 8
  /-- `MALLOC_ALIGNMENT`. -/
  align : Nat := 16
  /-- `MINSIZE`. -/
  minSize : Nat := 32
  /-- `TCACHE_MAX_BINS` (`mp_.tcache_bins` by default). -/
  tcacheBins : Nat := 64
  /-- `TCACHE_FILL_COUNT` (`mp_.tcache_count` by default). -/
  tcacheCount : Nat := 7
  /-- Width in bytes of a `tcache_perthread_struct` count (`uint16_t` since 2.30, `char` before). -/
  tcacheCountWidth : Nat := 2
  /-- `mp_.tcache_max_bytes` by default (`tidx2usize (TCACHE_MAX_BINS - 1)`). -/
  tcacheMaxBytes : Nat := 0x408
  /-- `tcache_unsorted_limit` by default (0: no limit). -/
  tcacheUnsortedLimit : Nat := 0
  /-- `NFASTBINS`. -/
  nFast : Nat := 10
  /-- `global_max_fast` after `malloc_init_state` (`DEFAULT_MXFAST`). -/
  maxFast : Nat := 0x80
  /-- `NBINS` (bin 0 unused, bin 1 unsorted, bins 2–63 small, 64–126 large, bin 127 a sentinel
  that no size maps to but `malloc_init_state` initialises: W17/M1). -/
  nBins : Nat := 128
  /-- `NSMALLBINS`. -/
  nSmallBins : Nat := 64
  /-- `MIN_LARGE_SIZE`. -/
  minLargeSize : Nat := 0x400
  /-- `DEFAULT_MMAP_THRESHOLD`, `DEFAULT_TRIM_THRESHOLD`, `DEFAULT_TOP_PAD`. -/
  mmapThreshold : Nat := 0x20000
  trimThreshold : Nat := 0x20000
  topPad : Nat := 0x20000
  /-- `DEFAULT_MMAP_THRESHOLD_MAX` (64-bit). -/
  mmapThresholdMax : Nat := 0x2000000
  /-- `DEFAULT_MMAP_MAX`. -/
  mmapMax : Nat := 0x10000
  /-- `FASTBIN_CONSOLIDATION_THRESHOLD`. -/
  consolidationThreshold : Nat := 0x10000
  /-- `MAX_ITERS` of `_int_malloc`'s unsorted scan. -/
  unsortedMaxIters : Nat := 10000
  /-- `HEAP_MAX_SIZE` of a non-main arena's heap (64-bit, `2 * DEFAULT_MMAP_THRESHOLD_MAX`). -/
  heapMaxSize : Nat := 0x4000000
  /-- `arena_test` default (64-bit: `NARENAS_FROM_NCORES (1)`). -/
  arenaTest : Nat := 8
  /-- `sizeof (heap_info)` (2.39: `ar_ptr`, `prev`, `size`, `mprotect_size`, `pagesize`, padded to
  `MALLOC_ALIGNMENT`): where a non-main heap's first chunk starts. An algorithm constant, since
  it places the top chunk of a new heap. -/
  heapInfoSize : Nat := 48
  /-- `sizeof (struct malloc_state)` (2.39 LP64: 0x898): a new arena's struct sits after its
  heap's `heap_info`, and its top chunk after the struct. -/
  stateSize : Nat := 0x898
  /-- `MMAP_AS_MORECORE_SIZE`: the least `sysmalloc`'s `mmap` fallback maps. -/
  mmapAsMorecore : Nat := 0x100000
  /-- The page size the allocator assumes (`GLRO (dl_pagesize)`). -/
  page : Nat := 4096
  /-- Safe-linking (`PROTECT_PTR`) of the tcache and fastbin lists (2.32+). -/
  safeLinking : Bool := true
  /-- What `tcache_key` holds (see `KeyKind`). -/
  keyKind : KeyKind := .random
  /-- `tcache_get` checks the entry's alignment (`aligned_OK`, 2.32+). -/
  tcacheAlignCheck : Bool := true
  /-- `sysmalloc` names its anonymous mappings with `prctl (PR_SET_VMA, …)` (2.39+,
  `__set_vma_name`); an environment fact, not an algorithm one, but the call sites move. -/
  vmaName : Bool := true
  /-- Source-level behaviours that changed between versions (see `Quirks`). -/
  quirks : Quirks := {}
  deriving DecidableEq, Repr

namespace Config

variable (C : Config)

/-- `MALLOC_ALIGN_MASK`. -/
def alignMask : Nat := C.align - 1

/-- `PREV_INUSE`, `IS_MMAPPED`, `NON_MAIN_ARENA`. -/
def prevInuse : Nat := 1
def isMmapped : Nat := 2
def nonMainArena : Nat := 4

/-- The chunk header's size (`prev_size` + `size`). -/
def hdr : Nat := 2 * C.sizeSz

/-- `request2size`. -/
def request2size (n : Nat) : Nat :=
  if n + C.sizeSz + C.alignMask < C.minSize then C.minSize
  else (n + C.sizeSz + C.alignMask) / C.align * C.align

/-- `checked_request2size`: `none` when the request exceeds `PTRDIFF_MAX`. -/
def checkedRequest2size (n : Nat) : Option Nat :=
  if n > 2 ^ 63 - 1 then none else some (C.request2size n)

/-- `csize2tidx`. -/
def tidx (size : Nat) : Nat := (size - C.minSize + C.align - 1) / C.align

/-- `usize2tidx`: the tcache bin serving a request of `n` bytes. -/
def utidx (n : Nat) : Nat := C.tidx (C.request2size n)

/-- `fastbin_index` (64-bit: `(sz >> 4) - 2`). -/
def fidx (size : Nat) : Nat := size / (2 * C.sizeSz) - 2

/-- `in_smallbin_range`. -/
def inSmallRange (size : Nat) : Bool := decide (size < C.minLargeSize)

/-- `largebin_index_64`. -/
def largeIndex (size : Nat) : Nat :=
  if size / 64 ≤ 48 then 48 + size / 64
  else if size / 512 ≤ 20 then 91 + size / 512
  else if size / 4096 ≤ 10 then 110 + size / 4096
  else if size / 32768 ≤ 4 then 119 + size / 32768
  else if size / 262144 ≤ 2 then 124 + size / 262144
  else 126

/-- `bin_index`: `smallbin_index` below `MIN_LARGE_SIZE`, else `largebin_index_64`. -/
def binIndex (size : Nat) : Nat :=
  if C.inSmallRange size then size / C.align else largeIndex size

/-- `PROTECT_PTR (pos, ptr)` when safe-linking is on, `ptr` otherwise. -/
def protect (pos ptr : Nat) : Nat :=
  if C.safeLinking then (pos / 4096) ^^^ ptr else ptr

/-- `REVEAL_PTR`: the inverse of `protect` at the same position. -/
def reveal (pos v : Nat) : Nat := C.protect pos v

/-- The last regular bin a size maps to (`NBINS - 2`): bin `nBins - 1` is only a sentinel. -/
def lastBin : Nat := C.nBins - 2

/-- **The sanity conditions** every theorem above x86 assumes. Decidable; each pinned
`Config` discharges it by `decide` (`Silmaril.Libc.Ptmalloc.Version.Thms`). -/
structure Ok : Prop where
  sizeSz : C.sizeSz = 8
  align : C.align = 16
  minSize : C.minSize = 32
  tcache : 0 < C.tcacheBins ∧ C.tcacheBins ≤ 64 ∧ 0 < C.tcacheCount ∧ C.tcacheCount < 2 ^ 15
  tcacheMax : C.tcacheMaxBytes + C.sizeSz + C.alignMask < C.minSize + C.align * C.tcacheBins
  fast : 0 < C.nFast ∧ C.maxFast < C.minLargeSize ∧ C.fidx C.maxFast < C.nFast
  bins : C.nBins = 128 ∧ C.nSmallBins = 64 ∧ C.minLargeSize = C.nSmallBins * C.align
  page : C.page = 4096
  thresholds : C.mmapThreshold ≤ C.mmapThresholdMax ∧ C.minSize ≤ C.trimThreshold
  /-- `free`'s dynamic threshold never lowers the thresholds below their defaults (M7's
  `MmapWF.trimMin`): the mmap threshold is page-aligned (so `sz + IS_MMAPPED > thr` with `sz`
  page-aligned gives `thr ≤ sz`) and `2 * mmap_threshold` covers the trim default. -/
  dynThreshold : C.mmapThreshold % C.page = 0 ∧ C.trimThreshold ≤ 2 * C.mmapThreshold
  /-- The non-main heap header and the `mmap` fallback unit are aligned. -/
  heapInfo : C.heapInfoSize % C.align = 0 ∧ C.mmapAsMorecore % C.page = 0
  /-- The thresholds are words (`mp_`'s fields; W16b): `2 * DEFAULT_MMAP_THRESHOLD_MAX < 2 ^ 64`. -/
  words : C.mmapThresholdMax < 2 ^ 63
  /-- A new arena fits its first heap (`malloc_state` non-empty, `heap_info` + struct + a
  minimal top within `HEAP_MIN_SIZE`), and heaps are page-aligned reservations. -/
  arena : 0 < C.stateSize ∧ C.heapInfoSize + C.stateSize + 64 ≤ 0x8000 ∧
    C.heapMaxSize % C.page = 0 ∧ C.page ≤ C.heapMaxSize
  /-- `heap_info` is not empty (a heap's first byte is its header, never a chunk). -/
  heapInfoPos : 0 < C.heapInfoSize

instance : Decidable C.Ok :=
  decidable_of_iff (C.sizeSz = 8 ∧ C.align = 16 ∧ C.minSize = 32 ∧
      (0 < C.tcacheBins ∧ C.tcacheBins ≤ 64 ∧ 0 < C.tcacheCount ∧ C.tcacheCount < 2 ^ 15) ∧
      C.tcacheMaxBytes + C.sizeSz + C.alignMask < C.minSize + C.align * C.tcacheBins ∧
      (0 < C.nFast ∧ C.maxFast < C.minLargeSize ∧ C.fidx C.maxFast < C.nFast) ∧
      (C.nBins = 128 ∧ C.nSmallBins = 64 ∧ C.minLargeSize = C.nSmallBins * C.align) ∧
      C.page = 4096 ∧ (C.mmapThreshold ≤ C.mmapThresholdMax ∧ C.minSize ≤ C.trimThreshold) ∧
      (C.mmapThreshold % C.page = 0 ∧ C.trimThreshold ≤ 2 * C.mmapThreshold) ∧
      (C.heapInfoSize % C.align = 0 ∧ C.mmapAsMorecore % C.page = 0) ∧
      C.mmapThresholdMax < 2 ^ 63 ∧
      (0 < C.stateSize ∧ C.heapInfoSize + C.stateSize + 64 ≤ 0x8000 ∧
        C.heapMaxSize % C.page = 0 ∧ C.page ≤ C.heapMaxSize) ∧ 0 < C.heapInfoSize)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o⟩⟩

end Config

/-- The LP64 defaults shared by glibc 2.32–2.40 (every field at its default): the same on
x86-64, riscv64 and arm64 (DWARF- and data-checked by the port-rv64 agent). The per-pin records
in `Silmaril.Libc.Ptmalloc.Version` start from it and override what differs. -/
def Config.lp64 : Config := {}

/-- The x86-64 configuration (= `Config.lp64`). -/
abbrev Config.x86_64 : Config := Config.lp64

end Silmaril.Libc.Ptmalloc
