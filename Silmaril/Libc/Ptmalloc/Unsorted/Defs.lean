module

public import Silmaril.Libc.Ptmalloc.Chunk.Defs

/-!
# ptmalloc component: the unsorted bin and `last_remainder` (per arena)

State `UnsortedSt` (bin 1, head first, and `last_remainder`), invariant `UnsortedWF` against the
**unsorted view**, operations `pushFront` (`_int_free`, remainders), `takeLast` (`_int_malloc`'s
scan takes `unsorted_chunks (av)->bk`), `setLastRem`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- **The unsorted bin** and `last_remainder`. -/
structure UnsortedSt where
  list : List Nat
  lastRem : Nat

namespace UnsortedSt

variable (us : UnsortedSt)

/-- Insert at the head. -/
def pushFront (a : Nat) : UnsortedSt := { us with list := a :: us.list }

/-- Take the last chunk (the scan's victim). -/
def takeLast : Option (Nat × UnsortedSt) :=
  match us.list.getLast? with
  | none => none
  | some a => some (a, { us with list := us.list.dropLast })

/-- Remove chunk `a` (`unlink_chunk` of an unsorted chunk: coalescing with a neighbour). -/
def remove (a : Nat) : UnsortedSt := { us with list := us.list.erase a }

/-- Set `last_remainder`. -/
def setLastRem (a : Nat) : UnsortedSt := { us with lastRem := a }

end UnsortedSt

/-- **The unsorted bin's invariant** against the unsorted view `cs` (W15a: `last_remainder` a
pointer). -/
structure UnsortedWF (C : Config) (us : UnsortedSt) (cs : List Chunk) : Prop where
  exact : ListExact us.list cs (.bin 1)
  nodup : us.list.Nodup
  size : ∀ c ∈ cs, C.minSize ≤ c.size
  lastRemBound : us.lastRem < 2 ^ 64

end Silmaril.Libc.Ptmalloc
