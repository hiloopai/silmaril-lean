module

public import Silmaril.Data.Layout.Bits.Defs

/-!
# glibc 2.39 malloc structures as `Silmaril.Data.Layout` declarations

`malloc_chunk`, `malloc_state` (the type of `main_arena`), `malloc_par` (the type of `mp_`),
`tcache_entry` and `tcache_perthread_struct`, as written in glibc 2.39 `malloc/malloc.c`
(and `sysdeps/generic/malloc-size.h` for `INTERNAL_SIZE_T`), after preprocessing for a
Linux build with `USE_TCACHE`: `INTERNAL_SIZE_T` is `size_t`, `__libc_lock_define (, mutex)` is
`__libc_lock_t mutex` (an `int`), `NBINS` is 128 and `TCACHE_MAX_BINS` is 64.
The only data-model-dependent array bound is `NFASTBINS` (`nfastbins`): 10 with 8-byte
`size_t`, 11 with 4-byte `size_t`.

Typedef names follow the DWARF of Ubuntu's `libc6` 2.39-0ubuntu8.9 so that the declarations
render as `gdb`'s `ptype` prints them (`Silmaril.Data.Layout.Glibc.Malloc.Thms`); the offsets are
checked there against the DWARF of the x86-64, AArch64, RISC-V 64 and i386 builds.

`mchunk_size` carries the flag bits `PREV_INUSE`, `IS_MMAPPED`, `NON_MAIN_ARENA`; its bit-level
specification is `Silmaril.Data.Layout.Glibc.Malloc.chunkSizeSpec` (in `Bits`).
-/

@[expose] public section

namespace Silmaril.Data.Layout.Glibc.Malloc

/-- `size_t` (`INTERNAL_SIZE_T`). -/
def sizeT : CTy := .typedef "size_t" (.int .size .unsigned)
/-- `uintptr_t`. -/
def uintptrT : CTy := .typedef "uintptr_t" (.int .intptr .unsigned)
/-- `uint16_t`. -/
def uint16T : CTy := .typedef "uint16_t" (.int (.exact 2) .unsigned)
/-- `__libc_lock_t`, an `int` on Linux (NPTL lll lock). -/
def lockT : CTy := .typedef "__libc_lock_t" (.int .int .signed)
def chunkPtr : CTy := .ptr (.struct "malloc_chunk")
/-- `mchunkptr`. -/
def mchunkptr : CTy := .typedef "mchunkptr" chunkPtr
/-- `mfastbinptr`. -/
def mfastbinptr : CTy := .typedef "mfastbinptr" chunkPtr
/-- `tcache_entry`. -/
def tcacheEntryT : CTy := .typedef "tcache_entry" (.struct "tcache_entry")

/-- `NBINS`. -/
def nbins : Nat := 128
/-- `TCACHE_MAX_BINS`. -/
def tcacheMaxBins : Nat := 64
/-- `BINMAPSIZE = NBINS / BITSPERMAP`. -/
def binmapSize : Nat := 4

/-- `SIZE_SZ`: the size of `INTERNAL_SIZE_T`. -/
def sizeSz (dm : DataModel) : Nat := ((dm.intShape .size).map (·.size)).getD 0

/-- `MALLOC_ALIGNMENT`: 16 on x86-64, AArch64, RISC-V 64 and (since 2.26) i386. -/
def mallocAlignment (_dm : DataModel) : Nat := 16

/-- `MINSIZE = (MIN_CHUNK_SIZE + MALLOC_ALIGN_MASK) & ~MALLOC_ALIGN_MASK`,
`MIN_CHUNK_SIZE = offsetof (struct malloc_chunk, fd_nextsize) = 4 * SIZE_SZ`. -/
def minSize (dm : DataModel) : Nat :=
  let a := mallocAlignment dm
  (4 * sizeSz dm + a - 1) / a * a

/-- `request2size`. -/
def request2size (dm : DataModel) (req : Nat) : Nat :=
  let a := mallocAlignment dm
  if req + sizeSz dm + (a - 1) < minSize dm then minSize dm
  else (req + sizeSz dm + (a - 1)) / a * a

/-- `fastbin_index (sz) = (sz >> (SIZE_SZ == 8 ? 4 : 3)) - 2`. -/
def fastbinIndex (dm : DataModel) (sz : Nat) : Nat :=
  sz / 2 ^ (if sizeSz dm = 8 then 4 else 3) - 2

/-- `NFASTBINS = fastbin_index (request2size (MAX_FAST_SIZE)) + 1`,
`MAX_FAST_SIZE = 80 * SIZE_SZ / 4`. -/
def nfastbins (dm : DataModel) : Nat :=
  fastbinIndex dm (request2size dm (80 * sizeSz dm / 4)) + 1

/-- ```
struct malloc_chunk {
  INTERNAL_SIZE_T      mchunk_prev_size;
  INTERNAL_SIZE_T      mchunk_size;
  struct malloc_chunk* fd;
  struct malloc_chunk* bk;
  struct malloc_chunk* fd_nextsize;
  struct malloc_chunk* bk_nextsize;
};
``` -/
def mallocChunk : Decl where
  kind := .struct
  tag := "malloc_chunk"
  fields := [
    { name := "mchunk_prev_size", ty := sizeT },
    { name := "mchunk_size", ty := sizeT },
    { name := "fd", ty := chunkPtr },
    { name := "bk", ty := chunkPtr },
    { name := "fd_nextsize", ty := chunkPtr },
    { name := "bk_nextsize", ty := chunkPtr }]

/-- `struct malloc_state` (`malloc.c`, 2.39), with `NFASTBINS = nfast`. -/
def mallocState (nfast : Nat) : Decl where
  kind := .struct
  tag := "malloc_state"
  fields := [
    { name := "mutex", ty := lockT },
    { name := "flags", ty := .int .int .signed },
    { name := "have_fastchunks", ty := .int .int .signed },
    { name := "fastbinsY", ty := .array mfastbinptr nfast },
    { name := "top", ty := mchunkptr },
    { name := "last_remainder", ty := mchunkptr },
    { name := "bins", ty := .array mchunkptr (nbins * 2 - 2) },
    { name := "binmap", ty := .array (.int .int .unsigned) binmapSize },
    { name := "next", ty := .ptr (.struct "malloc_state") },
    { name := "next_free", ty := .ptr (.struct "malloc_state") },
    { name := "attached_threads", ty := sizeT },
    { name := "system_mem", ty := sizeT },
    { name := "max_system_mem", ty := sizeT }]

/-- `struct malloc_par` (`malloc.c`, 2.39, `USE_TCACHE`). -/
def mallocPar : Decl where
  kind := .struct
  tag := "malloc_par"
  fields := [
    { name := "trim_threshold", ty := .int .long .unsigned },
    { name := "top_pad", ty := sizeT },
    { name := "mmap_threshold", ty := sizeT },
    { name := "arena_test", ty := sizeT },
    { name := "arena_max", ty := sizeT },
    { name := "thp_pagesize", ty := sizeT },
    { name := "hp_pagesize", ty := sizeT },
    { name := "hp_flags", ty := .int .int .signed },
    { name := "n_mmaps", ty := .int .int .signed },
    { name := "n_mmaps_max", ty := .int .int .signed },
    { name := "max_n_mmaps", ty := .int .int .signed },
    { name := "no_dyn_threshold", ty := .int .int .signed },
    { name := "mmapped_mem", ty := sizeT },
    { name := "max_mmapped_mem", ty := sizeT },
    { name := "sbrk_base", ty := .ptr (.int .char .plain) },
    { name := "tcache_bins", ty := sizeT },
    { name := "tcache_max_bytes", ty := sizeT },
    { name := "tcache_count", ty := sizeT },
    { name := "tcache_unsorted_limit", ty := sizeT }]

/-- `struct tcache_entry` (`malloc.c`, 2.39). -/
def tcacheEntry : Decl where
  kind := .struct
  tag := "tcache_entry"
  fields := [
    { name := "next", ty := .ptr (.struct "tcache_entry") },
    { name := "key", ty := uintptrT }]

/-- `struct tcache_perthread_struct` (`malloc.c`, 2.39). -/
def tcachePerthread : Decl where
  kind := .struct
  tag := "tcache_perthread_struct"
  fields := [
    { name := "counts", ty := .array uint16T tcacheMaxBins },
    { name := "entries", ty := .array (.ptr tcacheEntryT) tcacheMaxBins }]

/-- The malloc tag environment of a data model. -/
def env (dm : DataModel) : Env :=
  [mallocChunk, mallocState (nfastbins dm), mallocPar, tcacheEntry, tcachePerthread]

/-- Layouts of the five structures under a data model. -/
def chunkLayout (dm : DataModel) := declLayout dm (env dm) mallocChunk
def stateLayout (dm : DataModel) := declLayout dm (env dm) (mallocState (nfastbins dm))
def parLayout (dm : DataModel) := declLayout dm (env dm) mallocPar
def tcacheEntryLayout (dm : DataModel) := declLayout dm (env dm) tcacheEntry
def tcacheLayout (dm : DataModel) := declLayout dm (env dm) tcachePerthread

/-! ## The size field -/

/-- `mchunk_size` bit by bit: `PREV_INUSE` (bit 0), `IS_MMAPPED` (bit 1), `NON_MAIN_ARENA`
(bit 2); chunk sizes are multiples of `MALLOC_ALIGNMENT` = 16, so bit 3 is zero and the size
is `size16 * 16`. -/
def chunkSizeSpec (dm : DataModel) : WordSpec where
  width := 8 * sizeSz dm
  items := [
    ⟨"PREV_INUSE", ⟨0, 1⟩, .flag⟩,
    ⟨"IS_MMAPPED", ⟨1, 1⟩, .flag⟩,
    ⟨"NON_MAIN_ARENA", ⟨2, 1⟩, .flag⟩,
    ⟨"MALLOC_ALIGNMENT", ⟨3, 1⟩, .zero⟩,
    ⟨"size16", ⟨4, 8 * sizeSz dm - 4⟩, .value⟩]

/-- `chunksize (p) = p->mchunk_size & ~SIZE_BITS` (`SIZE_BITS = 7`). -/
def chunksize (v : Nat) : Nat := v - v % 8

/-- `prev_inuse`. -/
def prevInuse (v : Nat) : Bool := v % 2 == 1

/-- `chunk_is_mmapped`. -/
def isMmapped (v : Nat) : Bool := v / 2 % 2 == 1

/-- `chunk_main_arena` is its negation. -/
def nonMainArena (v : Nat) : Bool := v / 4 % 2 == 1

end Silmaril.Data.Layout.Glibc.Malloc
