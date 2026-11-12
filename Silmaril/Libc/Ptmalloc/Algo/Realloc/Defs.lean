module

public import Silmaril.Libc.Ptmalloc.Algo.Malloc.Defs

/-!
# ptmalloc algorithm: `_int_realloc`

glibc 2.39 `_int_realloc (av, oldp, oldsize, nb)` for a lent-out arena chunk:

1. `oldsize ≥ nb`: keep it, split below;
2. next is top and `oldsize + topsize ≥ nb + MINSIZE`: grow into top (`mergeTop` then `useTop`);
3. next is free and `oldsize + nextsize ≥ nb`: unlink it, fuse, split below;
4. else `_int_malloc (av, nb - MALLOC_ALIGN_MASK)` (0: fail), and if the new chunk is the next
   chunk (top was grown and carved in place) fuse and split below, else copy and
   `_int_free (av, oldp, 1)`;
5. split below: a remainder of at least `MINSIZE` is cut off in use and `_int_free`d (it may go
   to the tcache or a fastbin, or be coalesced).

Contents are not modelled (the copy is not visible at this level).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable (C : Config)

/-- **Split below**: the lent-out chunk at `p` (size `size ≥ nb`) keeps `nb` bytes; a remainder
of at least `MINSIZE` is cut off and freed. -/
def reallocSplit (l : Local) (p size nb : Nat) : Res (Nat × Local) := do
  if size - nb < C.minSize then return (p + C.hdr, l)
  let l := withTiles l (l.av.tiles.split p nb .client .client)
  let l ← intFree C l (p + nb)
  return (p + C.hdr, l)

/-- **`_int_realloc (av, oldp, oldsize, nb)`**: the new payload (0: refused). -/
def intRealloc (l : Local) (oldp oldsize nb : Nat) : Res (Nat × Local) := do
  let some loc := l.av.tiles.locate oldp | .error .reallocInvalid
  if loc.self.use ≠ .client ∨ oldsize ≠ loc.self.size then .error .reallocInvalid
  if nb ≤ oldsize then return ← reallocSplit C l oldp oldsize nb
  match loc.next with
  | .top =>
    let ts := l.av.tiles
    if nb + C.minSize ≤ oldsize + ts.topSize then
      return (oldp + C.hdr, withTiles l (ts.mergeTop.useTop nb .client))
  | .chunk n =>
    if n.use.tagFree ∧ nb ≤ oldsize + n.size then
      let l ← unlink l n.addr .internal
      return ← reallocSplit C (fuse l oldp .client) oldp (oldsize + n.size) nb
  | .fence => pure ()
  -- allocate, copy, free
  let (p, l) ← intMalloc C l (nb - C.alignMask)
  if p = 0 then return (0, l)
  let newp := p - C.hdr
  if newp = oldp + oldsize then
    let size := oldsize + l.av.tiles.sizeAt newp
    return ← reallocSplit C (fuse l oldp .client) oldp size nb
  let l ← intFree C l oldp
  return (p, l)

end Silmaril.Libc.Ptmalloc.Algo
