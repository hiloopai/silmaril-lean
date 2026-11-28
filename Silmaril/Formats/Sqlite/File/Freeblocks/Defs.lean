module

public import Silmaril.Formats.Sqlite.File.Defs

@[expose] public section

namespace Silmaril.Formats.Sqlite.File.Freeblocks

open Silmaril.Formats.Sqlite

structure Span where
  start : Nat
  stop : Nat

/-- Follow the ordered page-local freeblock chain with bounded fuel.
The zero pointer is the end marker, even when all fuel is spent. -/
def read? (view : File.View) (content : Nat) : Nat → Nat → Option (List Span)
  | 0, offset => if offset = 0 then some [] else none
  | fuel + 1, offset =>
    if offset = 0 then some [] else
      match view.be? offset 2, view.be? (offset + 2) 2 with
      | some next, some size =>
        if content ≤ offset ∧ 4 ≤ size ∧ offset + size ≤ view.length ∧
            (next = 0 ∨ offset + size ≤ next) then
          (read? view content fuel next).map (⟨offset, offset + size⟩ :: ·)
        else none
      | _, _ => none

/-- The headers in the source supply each block's length and the exact
pointer to the successor. A zero pointer ends the chain. -/
inductive Chain (view : File.View) : Nat → List Span → Prop where
  | nil : Chain view 0 []
  | cons {first size next : Nat} {rest : List Span} :
      first ≠ 0 → view.be? first 2 = some next → view.be? (first + 2) 2 = some size →
      Chain view next rest → Chain view first (⟨first, first + size⟩ :: rest)

/-- Validate the sorted union of occupied cells and freeblocks. The
zero-fragment profile requires exact consecutive extents. -/
def covers : Nat → Nat → List Span → Bool
  | lo, hi, [] => lo == hi
  | lo, hi, block :: rest => block.start == lo && decide (block.start < block.stop) &&
      covers block.stop hi rest

end Silmaril.Formats.Sqlite.File.Freeblocks
