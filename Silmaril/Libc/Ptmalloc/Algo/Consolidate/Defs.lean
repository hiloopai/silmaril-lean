module

public import Silmaril.Libc.Ptmalloc.Algo.Step.Defs

/-!
# ptmalloc algorithm: `malloc_consolidate`

glibc 2.39 `malloc_consolidate (av)`: clear `have_fastchunks`, then for each fastbin in index
order, for each chunk in list order: coalesce it with its free neighbours (backward, then into
top or forward) and put the result at the head of the unsorted bin.

glibc detaches a whole fastbin (`atomic_exchange_acquire (fb, NULL)`) and then walks the
detached chain; the model pops one chunk at a time (`FastSt.pop`). The two agree: coalescing
touches only chunks in regular bins and top, never a fast chunk (fast chunks are in use for the
boundary tags), so the not-yet-processed chunks of the bin are unaffected either way. Popping
keeps every intermediate state well formed (`Silmaril.Libc.Ptmalloc.Algo.Step`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable (C : Config)

/-- Consolidate fastbin `i`, one chunk at a time (`fuel` bounds the list length). -/
def consolidateBin (i : Nat) : Nat → Local → Res Local
  | 0, l => .ok l
  | fuel + 1, l =>
    match l.av.fast.pop i with
    | none => .ok l
    | some (p, fs) => do
      let l := { l with av := { l.av with fast := fs, tiles := l.av.tiles.relabel p .internal } }
      let (_, l) ← coalesce l p
      consolidateBin i fuel l

/-- **`malloc_consolidate (av)`**. -/
def consolidate (l : Local) : Res Local :=
  let l := { l with av := { l.av with fast := { l.av.fast with haveFast := false } } }
  (List.range C.nFast).foldlM (fun l i => consolidateBin i ((l.av.fast.lists i).length) l) l

end Silmaril.Libc.Ptmalloc.Algo
