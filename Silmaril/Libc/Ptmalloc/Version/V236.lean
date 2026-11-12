module

public import Silmaril.Libc.Ptmalloc.Version.Defs

/-!
# ptmalloc: glibc 2.36 (Debian 12, `libc6` 2.36-9+deb12u14)

The pin `debian_2_36_9_deb12u14` (`libc.so.6`
sha256 `6b4a4535…1421`, build id `93ac61ec…8a40`). Every number below is checked against the
generated `Versions.facts236` (`Silmaril.Libc.Ptmalloc.Version.Facts`) by
`Versions.pin236_matches` (`decide`).

## What differs from glibc 2.39 (`pin239`)

Sources compared: upstream `malloc/malloc.c` and `malloc/arena.c` at tags `glibc-2.36` and
`glibc-2.39` (sourceware git), plus the distribution patches touching them (Debian's
`git-updates.diff` up to deb12u14: the CVE-2026-0861 `_int_memalign` check and
`__get_nprocs`; Ubuntu 8.9: the same CVE patch). Binaries: the pinned files and their -dbg
symbols.

* **Config: algorithm constants** — none. Every `mp_` initial word, `DEFAULT_MXFAST`,
  `TCACHE_*`, `NBINS`, thresholds, safe-linking, the random `tcache_key`: as 2.39.
* **Config: `vmaName := false`** — no `__set_vma_name`/`prctl_supported` (2.39 names mappings).
* **Config: `quirks`** (algorithm behaviour, see `Quirks`): `unsortedTakeCheck` (one more abort
  in `_int_malloc`'s unsorted scan), no `reallocUsableFit`, no `reallocOldSizeCheck`,
  `fallbackArgsSwapped` (`sysmalloc_mmap_fallback`'s size rounding), no `memalignTcache`,
  `heapNoReserve`.
* **Layout** — identical DWARF layouts of `malloc_state`, `malloc_par`,
  `tcache_perthread_struct`, `malloc_chunk`, `tcache_entry`: `layout239` is reused.
* **Statics** — other addresses; `global_max_fast` is 8 bytes wide (`INTERNAL_SIZE_T`;
  1 byte in 2.39); no `prctl_supported`; TLS offsets of `tcache`, `thread_arena`,
  `tcache_shutting_down`, `errno` as 2.39 (0x48, 0x58, 0x50, 0x10).
* **Code** (gcc 12.2, no CET `endbr64`): every allocator function's instruction sequence
  differs from 2.39 (register allocation, inlining): `sysmalloc` and `new_heap` are out of line;
  `_int_free` inlines the 2.39 helpers `_int_free_merge_chunk`/`_int_free_maybe_consolidate`
  (2551 bytes against 1019); `_int_malloc` is 3756 bytes against 6289 (2.39 inlines
  `sysmalloc`). Block simulations are new for 2.36; the algorithm- and representation-level
  proofs are not.
* **Tunable ids** — all twelve differ (they are the build's tunable-list order).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Versions

/-- The source-level behaviours of glibc 2.36 (see `Quirks`). -/
def quirks236 : Quirks where
  unsortedTakeCheck := true
  reallocUsableFit := false
  reallocOldSizeCheck := false
  fallbackArgsSwapped := true
  memalignTcache := false
  heapNoReserve := true

/-- **The algorithm configuration of glibc 2.36**: the LP64 constants, no VMA naming, and the
2.36 quirks. -/
def config236 : Config := { Config.lp64 with vmaName := false, quirks := quirks236 }

/-- The struct layouts of glibc 2.36: identical to 2.39's (DWARF-checked). -/
def layout236 : Layout := layout239

/-- The statics of glibc 2.36. -/
def syms236 : Syms where
  mallocInitialized := 0x1da488
  tcacheKey := 0x1da478
  mainArena := 0x1d3c60
  mp := 0x1d3340
  globalMaxFast := 0x1da4a0
  perturbByte := 0x1da49c
  curbrk := 0x1db338
  singleThreaded := 0x1db5d8
  libcInitial := 0x1e1f4e
  alwaysFailMorecore := 0x1da4a8
  prctlSupported := none
  freeList := 0x1da490
  freeListLock := 0x1da498
  listLock := 0x1da48c
  narenas := 0x1d3328
  narenasLimit := 0x1da470
  got := [("tcache", 0x1d2d78), ("thread_arena", 0x1d2d70), ("tcache_shutting_down", 0x1d2d80),
    ("errno", 0x1d2de0), ("__curbrk", 0x1d2e30), ("_rtld_global_ro", 0x1d2e98),
    ("memset", 0x1d3168), ("memcpy", 0x1d3140), ("__tunable_get_val", 0x1d3158),
    ("__libc_enable_secure", 0x1d2e50)]
  tlsTcache := 0x48
  tlsArena := 0x58
  tlsShutdown := 0x50
  tlsErrno := 0x10
  imageEnd := 0x1e1f50
  globalMaxFastWidth := 8
  tunables := [("top_pad", 0xe), ("perturb_byte", 0x3), ("mmap_threshold", 0x1c),
    ("trim_threshold", 0x2), ("mmaps_max", 0x15), ("arena_max", 0x1b), ("arena_test", 0x1f),
    ("tcache_max", 0x23), ("tcache_count", 0x1e), ("tcache_unsorted_limit", 0x17),
    ("mxfast", 0xb), ("hugetlb", 0x9)]

/-- The entries of glibc 2.36 (`sysmalloc` out of line; no `_int_free` helpers, no
`__set_vma_name`). -/
def entries236 : Entries where
  malloc := 0x98930
  free := 0x98ef0
  calloc := 0x996e0
  realloc := 0x99130
  intMalloc := some 0x97360
  intFree := some 0x96120
  intRealloc := some 0x98340
  sysmalloc := some 0x96b20
  systrim := some 0x96070
  consolidate := some 0x95140
  tcacheInit := some 0x98210
  ptmallocInit := some 0x952f0
  unlinkChunk := some 0x95060
  sysmallocMmap := some 0x95ee0
  munmapChunk := some 0x949b0
  arenaGet2 := some 0x957a0

/-- **glibc 2.36** (Debian 12, `libc6` 2.36-9+deb12u14 amd64). -/
def pin236 : Pin where
  name := "debian_2_36_9_deb12u14"
  glibc := "2.36"
  sha256 := "6b4a45352fd0c540a9c7c718f35ce8c8e46a4e482f9d3885a910c32d1a0e1421"
  config := config236
  layout := layout236
  syms := syms236
  entries := entries236
  buildId := "93ac61ec5a8eb1396f9fbd350e3169a558528a40"
  compiler := "GCC (Debian 12.2.0-14+deb12u1) 12.2.0"

end Silmaril.Libc.Ptmalloc.Versions
