module

/-!
# ptmalloc: struct layouts (one per-version record)

The byte offsets of `malloc_state`, `malloc_par` and `tcache_perthread_struct` in one build. ONE
record per pin (`Silmaril.Libc.Ptmalloc.Version`), so moving to the struct-layout library
(`Silmaril.Data.Layout`) is a mechanical swap: each field becomes a
field lookup of the C struct's layout. Chunk fields are fixed by `SIZE_SZ` (`Config`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- **The byte offsets of glibc's allocator structs** in one build. -/
structure Layout where
  arMutex : Nat
  arFlags : Nat
  arHaveFast : Nat
  arFastbins : Nat
  arTop : Nat
  arLastRem : Nat
  arBins : Nat
  arBinmap : Nat
  arNext : Nat
  arNextFree : Nat
  arAttached : Nat
  arSystemMem : Nat
  arMaxSystemMem : Nat
  arSize : Nat
  mpTrim : Nat
  mpTopPad : Nat
  mpMmapThreshold : Nat
  mpArenaTest : Nat
  mpArenaMax : Nat
  mpNMmaps : Nat
  mpNMmapsMax : Nat
  mpMaxNMmaps : Nat
  mpNoDyn : Nat
  mpMmappedMem : Nat
  mpMaxMmappedMem : Nat
  mpSbrkBase : Nat
  mpTcacheBins : Nat
  mpTcacheMaxBytes : Nat
  mpTcacheCount : Nat
  mpTcacheUnsortedLimit : Nat
  mpSize : Nat
  tcCounts : Nat
  tcEntries : Nat
  tcStructSize : Nat
  deriving DecidableEq, Repr

end Silmaril.Libc.Ptmalloc
