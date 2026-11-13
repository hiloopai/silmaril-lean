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
   `_int_free (av, oldp, 1)` (`reallocCopy`);
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

/-- **Allocate, copy, free** (`_int_realloc`'s fallback): `_int_malloc (av, nb - MALLOC_ALIGN_MASK)`
(0: fail); if the new chunk is glibc's `next` (the chunk after the old one: the top chunk grown by
`sysmalloc` and carved in place, or a fastbin chunk), fuse it and split below, else copy and
`_int_free (av, oldp, 1)`.

`next` is computed before `_int_malloc` from the old chunk's address and size, so it is never a
chunk lent out before the call; and a chunk at `oldp + oldsize` is the old chunk's neighbour in the
tiling. States where either fails are ones the model's invariants exclude (`internal`): glibc's
`next` there is a fence post or a lent-out chunk, which `_int_malloc` never returns. -/
def reallocCopy (l : Local) (oldp oldsize nb : Nat) : Res (Nat × Local) := do
  let (p, l₁) ← intMalloc C l (nb - C.alignMask)
  if p = 0 then return (0, l₁)
  let newp := p - C.hdr
  if newp = oldp + oldsize then
    if l.av.chunks.any (fun c => c.addr = newp ∧ c.use = .client) then .error .internal
    else match l₁.av.tiles.locate oldp with
      | some ⟨_, _, .chunk n, _⟩ =>
        if n.addr = newp then reallocSplit C (fuse l₁ oldp .client) oldp (oldsize + n.size) nb
        else .error .internal
      | _ => .error .internal
  else
    let l₂ ← intFree C l₁ oldp
    return (p, l₂)

/-- **`_int_realloc (av, oldp, oldsize, nb)`**: the new payload (0: refused). -/
def intRealloc (l : Local) (oldp oldsize nb : Nat) : Res (Nat × Local) :=
  match l.av.tiles.locate oldp with
  | none => .error .reallocInvalid
  | some loc =>
    if loc.self.use ≠ .client ∨ oldsize ≠ loc.self.size then .error .reallocInvalid
    else if nb ≤ oldsize then reallocSplit C l oldp oldsize nb
    else match loc.next with
      | .top =>
        if nb + C.minSize ≤ oldsize + l.av.tiles.topSize then
          .ok (oldp + C.hdr, withTiles l (l.av.tiles.mergeTop.useTop nb .client))
        else reallocCopy C l oldp oldsize nb
      | .chunk n =>
        if n.use.tagFree ∧ nb ≤ oldsize + n.size then do
          let l₁ ← unlink l n.addr .internal
          reallocSplit C (fuse l₁ oldp .client) oldp (oldsize + n.size) nb
        else reallocCopy C l oldp oldsize nb
      | .fence => reallocCopy C l oldp oldsize nb

end Silmaril.Libc.Ptmalloc.Algo
