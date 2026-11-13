module

public import Silmaril.Data.NatRangeMap.Runs.Thms

/-!
# Finite range maps on `Nat`

`NatRangeMap α` is a finitely supported map `Nat → Option α`, stored as a
canonical run list (`Raw`, see `Runs/Defs.lean`): sorted, disjoint, non-empty
runs in relative coordinates, with no two directly adjacent runs carrying the
same value. Canonical run lists are determined by their lookups, so equality of
maps is structural equality of run lists (`DecidableEq`), and every finitely
supported map is represented (`Thms.lean`).

`assign r lo len1 v` and `erase r lo len1` rebuild only the runs below
`lo + len1 + 1` (linear in their number), merging equal neighbours; the runs above
are shared.
All operations are structurally recursive and kernel-reducible.
-/

@[expose] public section

namespace Silmaril.Data

universe u

/-- A finitely supported map `Nat → Option α`, as a canonical run list. -/
structure NatRangeMap (α : Type u) where
  raw : NatRangeMap.Raw α
  canonical : NatRangeMap.Raw.Canonical raw

namespace NatRangeMap

variable {α : Type u}

/-- The empty map. -/
def empty : NatRangeMap α := ⟨[], trivial⟩

instance : EmptyCollection (NatRangeMap α) := ⟨empty⟩
instance : Inhabited (NatRangeMap α) := ⟨empty⟩

/-- Lookup. -/
def find? (m : NatRangeMap α) (k : Nat) : Option α := Raw.find? m.raw k

/-- Map the keys `[lo, lo + len1]` to `v`. -/
def assign [DecidableEq α] (m : NatRangeMap α) (lo len1 : Nat) (v : α) : NatRangeMap α :=
  ⟨Raw.assign m.raw lo len1 v, Raw.canonical_assign m.canonical lo len1 v⟩

/-- Unmap the keys `[lo, lo + len1]`. -/
def erase [DecidableEq α] (m : NatRangeMap α) (lo len1 : Nat) : NatRangeMap α :=
  ⟨Raw.erase m.raw lo len1, Raw.canonical_erase m.canonical lo len1⟩

/-- The map `f` restricted to keys below `n`. -/
def ofFn [DecidableEq α] (f : Nat → Option α) (n : Nat) : NatRangeMap α :=
  ⟨Raw.ofFn f n, Raw.canonical_ofFn f n⟩

/-- Assign the entries `(lo, len1, val)` (keys `[lo, lo + len1]`) from last to
first, so earlier entries take precedence. Each assignment costs O(1) when the
entries are disjoint and in increasing order (as produced by `toList`). -/
def ofList [DecidableEq α] (l : List (Nat × Nat × α)) : NatRangeMap α :=
  ⟨Raw.ofList l, Raw.canonical_ofList l⟩

/-- Every key at or above `m.extent` is unmapped. -/
def extent (m : NatRangeMap α) : Nat := Raw.extent m.raw

/-- The maximal runs in absolute coordinates `(lo, len1, val)` (keys
`[lo, lo + len1]`), in increasing order. -/
def toList (m : NatRangeMap α) : List (Nat × Nat × α) := Raw.toList m.raw

/-- Equality is structural equality of the canonical run lists. -/
instance [DecidableEq α] : DecidableEq (NatRangeMap α) := fun a b =>
  if h : a.raw = b.raw then isTrue (by cases a; cases b; cases h; rfl)
  else isFalse fun e => h (congrArg raw e)

end NatRangeMap

end Silmaril.Data
