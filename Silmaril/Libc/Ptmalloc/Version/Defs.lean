module

public import Silmaril.Libc.Ptmalloc.Sim.Defs

/-!
# ptmalloc: per-pin version records

One `Pin` per pinned `libc.so.6`: the algorithm `Config`, the struct `Layout`, the static and
TLS offsets, and the entry addresses. **Everything a version changes is here**; the layers above
x86 take `pin.config` and `pin.layout`, and only `Silmaril.Libc.Ptmalloc.Sim.*` instances read the
addresses.

`pin239` is glibc 2.39 (Ubuntu `libc6` 2.39-0ubuntu8.9, `libc.so.6` sha256 `3a15d668…98bf`):
`syms239` and the `ar*`/`mp*`/`tc*` offsets were read off the binary's DWARF, and every value
is checked against the generated facts (`Versions.pin239_matches`; `Task.versions.symbols`). glibc 2.36 (`debian_2_36_9_deb12u14`) and 2.40
(`ubuntu_2_40_1ubuntu3_1`) are the `versions` builder's.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

open Silmaril.Data

/-- **Static offsets** (from the load base) and TLS offsets (in libc's static TLS block) of one
build. -/
structure Syms where
  mallocInitialized : Nat
  tcacheKey : Nat
  mainArena : Nat
  mp : Nat
  globalMaxFast : Nat
  perturbByte : Nat
  curbrk : Nat
  singleThreaded : Nat
  libcInitial : Nat
  alwaysFailMorecore : Nat
  prctlSupported : Option Nat
  freeList : Nat
  freeListLock : Nat
  listLock : Nat
  narenas : Nat
  narenasLimit : Nat
  /-- GOT slots read by the allocator (TLS offsets, `__curbrk`, `_rtld_global_ro`, callees). -/
  got : List (String × Nat)
  tlsTcache : Nat
  tlsArena : Nat
  tlsShutdown : Nat
  tlsErrno : Nat
  imageEnd : Nat
  /-- Width in bytes of `global_max_fast` (`INTERNAL_SIZE_T` = 8 up to 2.36, `uint8_t` = 1 in
  2.39/2.40); `__malloc_initialized` is a 1-byte `bool` in all three. -/
  globalMaxFastWidth : Nat := 1
  /-- Tunable ids passed to `__tunable_get_val` (`ptmalloc_init`'s `TUNABLE_GET`s, keyed by
  the `_dl_tunable_set_*` callback; `decorate_maps` from `__set_vma_name`, 2.39+). The ids are
  the build's tunable-list order and differ between every pinned version, so a callee contract
  that depends on the id (M4: 4-byte write for `decorate_maps`) reads them from here. -/
  tunables : List (String × Nat) := []
  deriving DecidableEq, Repr

/-- **Entry addresses** (offsets from the load base): the public functions and the internal
helpers the block simulation names (`none`: not located yet). -/
structure Entries where
  malloc : Nat
  free : Nat
  calloc : Nat
  realloc : Nat
  intMalloc : Option Nat := none
  intFree : Option Nat := none
  intRealloc : Option Nat := none
  sysmalloc : Option Nat := none
  systrim : Option Nat := none
  consolidate : Option Nat := none
  tcacheInit : Option Nat := none
  ptmallocInit : Option Nat := none
  unlinkChunk : Option Nat := none
  /-- 2.39+: the out-of-line pieces of `_int_free` (2.36 inlines them into `_int_free`). -/
  intFreeMergeChunk : Option Nat := none
  intFreeMaybeConsolidate : Option Nat := none
  sysmallocMmap : Option Nat := none
  munmapChunk : Option Nat := none
  arenaGet2 : Option Nat := none
  /-- 2.39+: `__set_vma_name` (`prctl (PR_SET_VMA, …)`). -/
  setVmaName : Option Nat := none
  deriving DecidableEq, Repr

/-- **One pinned libc**: name, glibc version, file hash, and everything the layers need. -/
structure Pin where
  name : String
  glibc : String
  sha256 : String
  config : Config
  layout : Layout
  syms : Syms
  entries : Entries
  /-- GNU build id of the file (selects its `libc6-dbg` debug file). -/
  buildId : String := ""
  /-- The compiler recorded in the debug file's `.comment` (code generation differs with it). -/
  compiler : String := ""

namespace Pin

variable (P : Pin)

/-- The relocated statics at load base `base`. -/
def statics (base : Nat) : Statics where
  mp := base + P.syms.mp
  mallocInitialized := base + P.syms.mallocInitialized
  tcacheKey := base + P.syms.tcacheKey
  globalMaxFast := base + P.syms.globalMaxFast
  perturbByte := base + P.syms.perturbByte
  freeList := base + P.syms.freeList
  narenas := base + P.syms.narenas
  globalMaxFastWidth := P.syms.globalMaxFastWidth

/-- The calling thread's TLS variables, for thread pointer `tp` and libc's block at `tp - off`. -/
def tlsAddrs (tp off : Nat) : TlsAddrs where
  tcache := tp - off + P.syms.tlsTcache
  arena := tp - off + P.syms.tlsArena
  shutdown := tp - off + P.syms.tlsShutdown
  errno := tp - off + P.syms.tlsErrno

/-- The surroundings' addresses, x86-64 conventions (`__libc_single_threaded`, the canary at
`%fs:0x28`); an RV64/AArch64 pin overrides `singleAddr`/`singleWidth`/`singleVal`/`multiVal`
and `canary`. -/
def envAddrs (base tp : Nat) : EnvAddrs where
  curbrk := base + P.syms.curbrk
  singleAddr := base + P.syms.singleThreaded
  libcInitial := base + P.syms.libcInitial
  alwaysFailMorecore := base + P.syms.alwaysFailMorecore
  prctlSupported := P.syms.prctlSupported.map (base + ·)
  narenasLimit := base + P.syms.narenasLimit
  freeListLock := base + P.syms.freeListLock
  listLock := base + P.syms.listLock
  canary := tp + 0x28
  mp := base + P.syms.mp

/-- Everything `Sim` needs for this pin, at load base `base` and thread pointer `tp`. -/
def repAt (base tp off : Nat) : RepAt :=
  ⟨P.layout, P.statics base, P.tlsAddrs tp off, P.envAddrs base tp⟩

/-- `main_arena`'s address at load base `base`. -/
def mainArena (base : Nat) : Nat := base + P.syms.mainArena

end Pin

/-! ## glibc 2.39 (Ubuntu 2.39-0ubuntu8.9) -/

/-- The struct layouts of glibc 2.39 (x86-64). -/
def layout239 : Layout where
  arMutex := 0x0
  arFlags := 0x4
  arHaveFast := 0x8
  arFastbins := 0x10
  arTop := 0x60
  arLastRem := 0x68
  arBins := 0x70
  arBinmap := 0x860
  arNext := 0x870
  arNextFree := 0x878
  arAttached := 0x880
  arSystemMem := 0x888
  arMaxSystemMem := 0x890
  arSize := 0x898
  mpTrim := 0x0
  mpTopPad := 0x8
  mpMmapThreshold := 0x10
  mpArenaTest := 0x18
  mpArenaMax := 0x20
  mpNMmaps := 0x3c
  mpNMmapsMax := 0x40
  mpMaxNMmaps := 0x44
  mpNoDyn := 0x48
  mpMmappedMem := 0x50
  mpMaxMmappedMem := 0x58
  mpSbrkBase := 0x60
  mpTcacheBins := 0x68
  mpTcacheMaxBytes := 0x70
  mpTcacheCount := 0x78
  mpTcacheUnsortedLimit := 0x80
  mpSize := 0x88
  tcCounts := 0
  tcEntries := 0x80
  tcStructSize := 0x280

/-- The statics of glibc 2.39 (offsets from the load base). -/
def syms239 : Syms where
  mallocInitialized := 0x20b188
  tcacheKey := 0x20b178
  mainArena := 0x204ac0
  mp := 0x204180
  globalMaxFast := 0x20b1a0
  perturbByte := 0x20b19c
  curbrk := 0x20bd70
  singleThreaded := 0x20c040
  libcInitial := 0x212d8e
  alwaysFailMorecore := 0x20b1a1
  prctlSupported := some 0x204264
  freeList := 0x20b190
  freeListLock := 0x20b198
  listLock := 0x20b18c
  narenas := 0x204168
  narenasLimit := 0x20b170
  got := [("tcache", 0x203d98), ("thread_arena", 0x203d90), ("tcache_shutting_down", 0x203da0),
    ("errno", 0x203df8), ("__curbrk", 0x203e48), ("_rtld_global_ro", 0x203eb0),
    ("memset", 0x203d38), ("memcpy", 0x203cf0), ("__tunable_get_val", 0x203d28),
    ("__tunable_is_initialized", 0x203ce0), ("__libc_enable_secure", 0x203e68)]
  tlsTcache := 0x48
  tlsArena := 0x58
  tlsShutdown := 0x50
  tlsErrno := 0x10
  imageEnd := 0x212d90
  globalMaxFastWidth := 1
  tunables := [("top_pad", 0x21), ("perturb_byte", 0x1a), ("mmap_threshold", 0x1),
    ("trim_threshold", 0xe), ("mmaps_max", 0xc), ("arena_max", 0x26), ("arena_test", 0x17),
    ("tcache_max", 0x2), ("tcache_count", 0x1b), ("tcache_unsorted_limit", 0x5), ("mxfast", 0x0),
    ("hugetlb", 0x18), ("decorate_maps", 0x12)]

/-- The entries of glibc 2.39. -/
def entries239 : Entries where
  malloc := 0xad750
  free := 0xade30
  calloc := 0xae8a0
  realloc := 0xae1a0
  intMalloc := some 0xab650
  intFree := some 0xab250
  intRealloc := some 0xad030
  systrim := some 0xaab20
  tcacheInit := some 0xacef0
  ptmallocInit := some 0xa9e50
  unlinkChunk := some 0xa9bb0
  consolidate := some 0xa9c90
  intFreeMergeChunk := some 0xab070
  intFreeMaybeConsolidate := some 0xaabe0
  sysmallocMmap := some 0xaa980
  munmapChunk := some 0xa94e0
  arenaGet2 := some 0xaa3e0
  setVmaName := some 0x12a9d0

/-- **glibc 2.39**: every algorithm constant at the x86-64 default. -/
def pin239 : Pin where
  name := "ubuntu_2_39_0ubuntu8_9"
  glibc := "2.39"
  sha256 := "3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf"
  config := Config.lp64
  layout := layout239
  syms := syms239
  entries := entries239
  buildId := "a4a7992a8e66555c8141ab2a08a8465ff6e0ea65"
  compiler := "GCC (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0"

/-! ## Obligations (owned by `versions`) -/

/-- **`Task.versions.symbols`**: the pin's offsets are the binary's (DWARF / symbol table of the
pinned file): to be discharged per pin from the generated pin facts
(`Silmaril.Libc.Ptmalloc.Version.Facts`), never by hand. Stated as a
predicate on the record so each pin gets its own instance. -/
def Task.versions.symbols (P : Pin) (facts : List (String × Nat)) : Prop :=
  ∀ nm v, (nm, v) ∈ facts →
    (nm = "main_arena" → P.syms.mainArena = v) ∧ (nm = "mp_" → P.syms.mp = v) ∧
    (nm = "tcache_key" → P.syms.tcacheKey = v) ∧ (nm = "__curbrk" → P.syms.curbrk = v) ∧
    (nm = "malloc" → P.entries.malloc = v) ∧ (nm = "free" → P.entries.free = v) ∧
    (nm = "_int_malloc" → P.entries.intMalloc = some v) ∧ (nm = "_int_free" → P.entries.intFree = some v)

/-! ## Checking a record against the generated facts (`Silmaril.Libc.Ptmalloc.Version.Facts`) -/

namespace Versions

/-- The fact name of a GOT slot named in `Syms.got` (the generator names a slot after its
relocation's symbol). -/
def gotFactName : String → String
  | "errno" => "__libc_errno"
  | "memset" => "__GI_memset"
  | n => n

/-- **Everything a `Pin` claims about its file**, as fact keys with the expected value (`none`:
the symbol must be absent, e.g. a helper gcc inlined). Keys follow the generator's
scheme (`Silmaril.Libc.Ptmalloc.Version.Facts`). -/
def claims (P : Pin) : List (String × Option Nat) :=
  let C := P.config; let L := P.layout; let S := P.syms; let E := P.entries
  [("sym:main_arena", some S.mainArena), ("sym:mp_", some S.mp),
   ("sym:tcache_key", some S.tcacheKey), ("sym:__malloc_initialized", some S.mallocInitialized),
   ("size:__malloc_initialized", some 1),
   ("sym:global_max_fast", some S.globalMaxFast),
   ("size:global_max_fast", some S.globalMaxFastWidth),
   ("sym:perturb_byte", some S.perturbByte), ("sym:__curbrk", some S.curbrk),
   ("sym:__libc_single_threaded", some S.singleThreaded),
   ("sym:__libc_initial", some S.libcInitial),
   ("sym:__always_fail_morecore", some S.alwaysFailMorecore),
   ("sym:prctl_supported", S.prctlSupported), ("sym:free_list", some S.freeList),
   ("sym:free_list_lock", some S.freeListLock), ("sym:list_lock", some S.listLock),
   ("sym:narenas", some S.narenas), ("sym:narenas_limit", some S.narenasLimit),
   ("sym:tcache", some S.tlsTcache), ("sym:thread_arena", some S.tlsArena),
   ("sym:tcache_shutting_down", some S.tlsShutdown), ("sym:__libc_errno", some S.tlsErrno),
   ("image_end", some S.imageEnd),
   ("sym:__libc_malloc", some E.malloc), ("sym:__libc_free", some E.free),
   ("sym:__libc_calloc", some E.calloc), ("sym:__libc_realloc", some E.realloc),
   ("sym:_int_malloc", E.intMalloc), ("sym:_int_free", E.intFree),
   ("sym:_int_realloc", E.intRealloc), ("sym:sysmalloc", E.sysmalloc),
   ("sym:systrim", E.systrim),
   ("sym:malloc_consolidate", E.consolidate), ("sym:tcache_init", E.tcacheInit),
   ("sym:ptmalloc_init", E.ptmallocInit), ("sym:unlink_chunk", E.unlinkChunk),
   ("sym:_int_free_merge_chunk", E.intFreeMergeChunk),
   ("sym:_int_free_maybe_consolidate", E.intFreeMaybeConsolidate),
   ("sym:sysmalloc_mmap", E.sysmallocMmap), ("sym:munmap_chunk", E.munmapChunk),
   ("sym:arena_get2", E.arenaGet2), ("sym:__set_vma_name", E.setVmaName),
   ("malloc_state.mutex", some L.arMutex), ("malloc_state.flags", some L.arFlags),
   ("malloc_state.have_fastchunks", some L.arHaveFast),
   ("malloc_state.fastbinsY", some L.arFastbins), ("malloc_state.top", some L.arTop),
   ("malloc_state.last_remainder", some L.arLastRem), ("malloc_state.bins", some L.arBins),
   ("malloc_state.binmap", some L.arBinmap), ("malloc_state.next", some L.arNext),
   ("malloc_state.next_free", some L.arNextFree),
   ("malloc_state.attached_threads", some L.arAttached),
   ("malloc_state.system_mem", some L.arSystemMem),
   ("malloc_state.max_system_mem", some L.arMaxSystemMem),
   ("sizeof:malloc_state", some L.arSize),
   ("malloc_par.trim_threshold", some L.mpTrim), ("malloc_par.top_pad", some L.mpTopPad),
   ("malloc_par.mmap_threshold", some L.mpMmapThreshold),
   ("malloc_par.arena_test", some L.mpArenaTest), ("malloc_par.arena_max", some L.mpArenaMax),
   ("malloc_par.n_mmaps", some L.mpNMmaps), ("malloc_par.n_mmaps_max", some L.mpNMmapsMax),
   ("malloc_par.max_n_mmaps", some L.mpMaxNMmaps),
   ("malloc_par.no_dyn_threshold", some L.mpNoDyn),
   ("malloc_par.mmapped_mem", some L.mpMmappedMem),
   ("malloc_par.max_mmapped_mem", some L.mpMaxMmappedMem),
   ("malloc_par.sbrk_base", some L.mpSbrkBase), ("malloc_par.tcache_bins", some L.mpTcacheBins),
   ("malloc_par.tcache_max_bytes", some L.mpTcacheMaxBytes),
   ("malloc_par.tcache_count", some L.mpTcacheCount),
   ("malloc_par.tcache_unsorted_limit", some L.mpTcacheUnsortedLimit),
   ("sizeof:malloc_par", some L.mpSize),
   ("tcache_perthread_struct.counts", some L.tcCounts),
   ("tcache_perthread_struct.entries", some L.tcEntries),
   ("sizeof:tcache_perthread_struct", some L.tcStructSize),
   ("sizeof:malloc_chunk", some (6 * C.sizeSz)), ("malloc_chunk.mchunk_size", some C.sizeSz),
   ("malloc_chunk.fd", some C.hdr), ("sizeof:malloc_state", some C.stateSize),
   ("sizeof:_heap_info", some C.heapInfoSize),
   ("mp_init:trim_threshold", some C.trimThreshold), ("mp_init:top_pad", some C.topPad),
   ("mp_init:mmap_threshold", some C.mmapThreshold), ("mp_init:arena_test", some C.arenaTest),
   ("mp_init:n_mmaps_max", some C.mmapMax), ("mp_init:tcache_bins", some C.tcacheBins),
   ("mp_init:tcache_max_bytes", some C.tcacheMaxBytes),
   ("mp_init:tcache_count", some C.tcacheCount),
   ("mp_init:tcache_unsorted_limit", some C.tcacheUnsortedLimit)] ++
  S.got.map (fun x => ("got:" ++ gotFactName x.1, some x.2)) ++
  S.tunables.map (fun x => ("tunable:" ++ x.1, some x.2))

/-- **The record agrees with the facts**: every claim's key has exactly the claimed value
(`none`: the key is absent). Decidable; each pin proves it by `decide`. -/
def Matches (P : Pin) (facts : List (String × Nat)) : Prop :=
  ∀ c ∈ claims P, facts.lookup c.1 = c.2

instance (P : Pin) (facts : List (String × Nat)) : Decidable (Matches P facts) :=
  inferInstanceAs (Decidable (∀ c ∈ claims P, facts.lookup c.1 = c.2))

end Versions

end Silmaril.Libc.Ptmalloc
