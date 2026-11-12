module

public import Silmaril.Libc.Ptmalloc.Version.Defs

/-!
# ptmalloc: glibc 2.40 (Ubuntu 24.10, `libc6` 2.40-1ubuntu3.1)

The pin `ubuntu_2_40_1ubuntu3_1` (`libc.so.6`
sha256 `132ba50d…b204`, build id `91f01b4a…413d`). Every number below is checked against the
generated `Versions.facts240` by `Versions.pin240_matches` (`decide`).

## What differs from glibc 2.39 (`pin239`)

* **Sources**: upstream `malloc/malloc.c` and `malloc/arena.c` are byte-identical at tags
  `glibc-2.39` and `glibc-2.40`. Ubuntu's 2.40-1ubuntu3.1 patches touch no allocator source;
  Ubuntu's 2.39-0ubuntu8.9 adds CVE-2026-0861 (`_int_memalign` alignment check), which 2.40's
  pin lacks (`memalign` only; not an `Ops` path).
* **Config, quirks, Layout** — identical: `config240 = Config.lp64 = pin239.config`,
  `layout240 = layout239`.
* **Statics, GOT slots, entries** — other addresses only (same widths: `global_max_fast` 1
  byte; same TLS offsets).
* **Tunable ids** — 11 of the 13 differ (`perturb_byte` and `tcache_count` agree), including
  `decorate_maps` (0x12 → 0x20), which M4's `__tunable_get_val` contract keys on.
* **Code** (gcc 14.2 against 13.3): normalised listings (addresses dropped, branch targets as
  instruction labels, rip-relative operands as the symbol, nops dropped)
  are **identical** for `__libc_malloc`, `__libc_free`,
  `__libc_calloc`, `_int_free`, `_int_free_merge_chunk`, `tcache_init`, `malloc_consolidate`,
  `systrim`, `unlink_chunk`, `munmap_chunk`, `sysmalloc_mmap`, `arena_get_retry`, and every
  tunable callback. They differ only by scheduling in `__libc_realloc` (one `xor` moved),
  `_int_realloc` (one load moved), `get_free_list` (two loads moved),
  `sysmalloc_mmap_fallback` (`lea` operands swapped), by ids in `ptmalloc_init` and
  `__set_vma_name`, and substantially in `_int_malloc` (6192 bytes against 6289, 1382 against
  1407 instructions: scheduling and register allocation), `_int_free_maybe_consolidate`,
  `arena_get2`, `alloc_new_heap`, `_int_memalign`, `_mid_memalign`. So the tcache paths of
  `malloc` and `free` (and `_int_free`'s tcache put) are the 2.39 blocks at other addresses and
  displacements; `_int_malloc`'s tcache refill copies are new code.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Versions

/-- **The algorithm configuration of glibc 2.40**: the same as 2.39's. -/
def config240 : Config := Config.lp64

/-- The struct layouts of glibc 2.40: identical to 2.39's (DWARF-checked). -/
def layout240 : Layout := layout239

/-- The statics of glibc 2.40. -/
def syms240 : Syms where
  mallocInitialized := 0x218188
  tcacheKey := 0x218178
  mainArena := 0x211ac0
  mp := 0x211180
  globalMaxFast := 0x2181a0
  perturbByte := 0x21819c
  curbrk := 0x218d90
  singleThreaded := 0x219060
  libcInitial := 0x21fdd0
  alwaysFailMorecore := 0x2181a1
  prctlSupported := some 0x211264
  freeList := 0x218190
  freeListLock := 0x218198
  listLock := 0x21818c
  narenas := 0x211168
  narenasLimit := 0x218170
  got := [("tcache", 0x210da0), ("thread_arena", 0x210d98), ("tcache_shutting_down", 0x210da8),
    ("errno", 0x210e00), ("__curbrk", 0x210e50), ("_rtld_global_ro", 0x210eb8),
    ("memset", 0x210d40), ("memcpy", 0x210cf8), ("__tunable_get_val", 0x210d30),
    ("__tunable_is_initialized", 0x210ce8), ("__libc_enable_secure", 0x210e70)]
  tlsTcache := 0x48
  tlsArena := 0x58
  tlsShutdown := 0x50
  tlsErrno := 0x10
  imageEnd := 0x21fdd8
  globalMaxFastWidth := 1
  tunables := [("top_pad", 0x1e), ("perturb_byte", 0x1a), ("mmap_threshold", 0x18),
    ("trim_threshold", 0x1f), ("mmaps_max", 0x17), ("arena_max", 0x13), ("arena_test", 0x14),
    ("tcache_max", 0x1c), ("tcache_count", 0x1b), ("tcache_unsorted_limit", 0x1d),
    ("mxfast", 0x19), ("hugetlb", 0x16), ("decorate_maps", 0x20)]

/-- The entries of glibc 2.40 (the same out-of-line helpers as 2.39). -/
def entries240 : Entries where
  malloc := 0xb2c60
  free := 0xb3370
  calloc := 0xb3de0
  realloc := 0xb36e0
  intMalloc := some 0xb0bc0
  intFree := some 0xb07c0
  intRealloc := some 0xb2540
  systrim := some 0xb0060
  consolidate := some 0xaf1c0
  tcacheInit := some 0xb23f0
  ptmallocInit := some 0xaf380
  unlinkChunk := some 0xaf0e0
  intFreeMergeChunk := some 0xb05e0
  intFreeMaybeConsolidate := some 0xb0120
  sysmallocMmap := some 0xafec0
  munmapChunk := some 0xae9b0
  arenaGet2 := some 0xaf930
  setVmaName := some 0x134530

/-- **glibc 2.40** (Ubuntu 24.10, `libc6` 2.40-1ubuntu3.1 amd64). -/
def pin240 : Pin where
  name := "ubuntu_2_40_1ubuntu3_1"
  glibc := "2.40"
  sha256 := "132ba50d4abaeff314e64f5d84daa4e4e6d9b227135bc035fde1b69a81aab204"
  config := config240
  layout := layout240
  syms := syms240
  entries := entries240
  buildId := "91f01b4ad171c80b6303d08d1f08cba8b990413d"
  compiler := "GCC (Ubuntu 14.2.0-4ubuntu2) 14.2.0"

end Silmaril.Libc.Ptmalloc.Versions
