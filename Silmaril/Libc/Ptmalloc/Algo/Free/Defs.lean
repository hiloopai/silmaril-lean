module

public import Silmaril.Libc.Ptmalloc.Algo.Consolidate.Defs
public import Silmaril.Libc.Ptmalloc.Algo.Trim.Defs

/-!
# ptmalloc algorithm: `_int_free`

glibc 2.39 `_int_free (av, p, have_lock)` and its helpers `_int_free_merge_chunk`,
`_int_free_create_chunk`, `_int_free_maybe_consolidate`, for a chunk `p` of the arena's tiling
(`mmap`ed chunks never reach it: `__libc_free` handles them):

1. checks: `free(): invalid pointer` (misaligned or wrapping), `free(): invalid size`; the chunk
   must be lent out (`client`): a chunk already in a fastbin or regular bin is a double free;
2. **tcache**: with a tcache and `tc_idx < tcache_bins`, a chunk already in that tcache bin is
   `double free detected in tcache 2` (glibc finds it through `e->key == tcache_key`); a bin with
   room takes it (`tcache_put`);
3. **fastbin** (`size ≤ global_max_fast`): `double free or corruption (fasttop)` if it is the
   bin's head, else pushed, `have_fastchunks` set;
4. otherwise **merge** (`coalesce`: backward, into top or forward, unsorted head), then
   `_int_free_maybe_consolidate`: if the merged size reaches `FASTBIN_CONSOLIDATION_THRESHOLD`,
   `malloc_consolidate` when there are fast chunks, then `systrim (mp_.top_pad)` of the main arena
   when `chunksize (top) ≥ mp_.trim_threshold` (M7), or `heap_trim` of a non-main heap.

`TRIM_FASTBINS` is 0 in glibc's default build, so a fast chunk next to top still goes to its
fastbin.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable (C : Config)

/-- **`_int_free_maybe_consolidate (av, size)`**. -/
def maybeConsolidate (l : Local) (size : Nat) : Res Local := do
  if size < C.consolidationThreshold then return l
  let l ← if l.av.fast.haveFast then consolidate C l else pure l
  if l.isMain then
    if l.shared.mm.mp.trimThreshold ≤ l.av.tiles.topSize then systrim C l C.topPad else pure l
  else heapTrim C l C.topPad

/-- **The merge part** (`_int_free_merge_chunk`): the chunk at `c` is held `internal`, coalesced
and released. -/
def freeMerge (l : Local) (c : Nat) : Res Local := do
  let (size, l) ← coalesce (l.relabel c .internal) c
  maybeConsolidate C l size

/-- **`_int_free (av, p)`** of the chunk at `c`. -/
def intFree (l : Local) (c : Nat) : Res Local := do
  let some ch := l.av.tiles.find? c | .error .freeInvalidPointer
  let size := ch.size
  if c % C.align ≠ 0 ∨ 2 ^ 64 < c + size then .error .freeInvalidPointer
  if size < C.minSize ∨ size % C.align ≠ 0 then .error .freeInvalidSize
  match ch.use with
  | .fast _ => .error .doubleFreeFasttop
  | .bin _ => .error .doubleFreePrev
  | .internal => .error .freeInvalidPointer
  | .client =>
  let i := C.tidx size
  -- the tcache
  match l.thread.tcache with
  | some tc =>
    if i < C.tcacheBins then
      if (c, size) ∈ tc.bins i then .error .doubleFreeTcache
      else if (tc.bins i).length < C.tcacheCount then return tcPut l (c, size) i
  | none => pure ()
  -- the fastbins
  if size ≤ C.maxFast then
    let j := C.fidx size
    if (l.av.fast.lists j).head? = some c then .error .doubleFreeFasttop
    return l.fastPush c j
  -- merge
  freeMerge C l c

end Silmaril.Libc.Ptmalloc.Algo
