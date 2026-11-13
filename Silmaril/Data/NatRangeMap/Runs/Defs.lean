module

/-!
# Run lists: the raw representation of `NatRangeMap`

A `Raw α` is a list of runs in relative coordinates. Reading the list from a
base position `b` (initially `0`), a run `⟨gap, len1, val⟩` maps every key of
`[b + gap, b + gap + len1 + 1)` to `val`, and the next run is read from the base
`b + gap + len1 + 1`. Runs are therefore sorted, disjoint and non-empty by
construction, and every raw value denotes a finitely supported function
`Nat → Option α` (`find?`).

Raw values are not canonical: two adjacent runs with `gap = 0` and equal values
denote the same map as one merged run. `Canonical` forbids exactly this, and
`normalize` merges such runs; `assign`, `erase`, `ofList` and `ofFn` keep run
lists canonical by merging at the boundaries they touch. Canonical run lists are determined by their
lookups (`Silmaril.Data.NatRangeMap.Raw.eq_of_find?` in `Runs/Thms.lean`).

All functions here are structurally recursive and use only `Nat` arithmetic and
comparisons, so they reduce in the kernel, where `Nat` operations are
accelerated. For large maps prefer `decide +kernel` to the elaborator's `decide`
or `rfl`, and expect to raise `maxRecDepth` (kernel whnf recursion is as deep as
the chain of pending operations).
-/

@[expose] public section

namespace Silmaril.Data.NatRangeMap

universe u

/-- A non-empty run of `len1 + 1` keys mapped to `val`, starting `gap` keys
after the end of the previous run (or after `0` for the first run). -/
structure Run (α : Type u) where
  gap : Nat
  len1 : Nat
  val : α
  deriving DecidableEq, Repr

/-- Raw run lists, in relative coordinates. Not canonical. -/
abbrev Raw (α : Type u) := List (Run α)

namespace Raw

variable {α : Type u}

/-- Lookup. -/
def find? : Raw α → Nat → Option α
  | [], _ => none
  | ⟨g, l, v⟩ :: rs, k =>
    if k < g then none else if k ≤ g + l then some v else find? rs (k - (g + l + 1))

/-- The number of keys spanned by the runs and gaps: every key at or above it is
unmapped. -/
def extent : Raw α → Nat
  | [] => 0
  | ⟨g, l, _⟩ :: rs => g + l + 1 + extent rs

/-- Shift by `d`: add `d` to the first gap. -/
def addGap (d : Nat) : Raw α → Raw α
  | [] => []
  | ⟨g, l, v⟩ :: rs => ⟨d + g, l, v⟩ :: rs

/-- The restriction to keys below `n`. -/
def takeBelow : Raw α → Nat → Raw α
  | [], _ => []
  | ⟨g, l, v⟩ :: rs, n =>
    if n ≤ g then []
    else if n ≤ g + l then [⟨g, n - g - 1, v⟩]
    else ⟨g, l, v⟩ :: takeBelow rs (n - (g + l + 1))

/-- The keys at or above `n`, shifted down by `n`. -/
def dropBelow : Raw α → Nat → Raw α
  | [], _ => []
  | ⟨g, l, v⟩ :: rs, n =>
    if n ≤ g then ⟨g - n, l, v⟩ :: rs
    else if n ≤ g + l then ⟨0, g + l - n, v⟩ :: rs
    else dropBelow rs (n - (g + l + 1))

/-- No run after the first starts directly after its predecessor with the same
value. -/
def Canonical : Raw α → Prop
  | x :: y :: rs => (y.gap = 0 → x.val ≠ y.val) ∧ Canonical (y :: rs)
  | _ => True

instance decCanonical [DecidableEq α] : (r : Raw α) → Decidable (Canonical r)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | x :: y :: rs =>
    have := decCanonical (y :: rs)
    inferInstanceAs (Decidable ((y.gap = 0 → x.val ≠ y.val) ∧ Canonical (y :: rs)))

/-- Prepend a run, merging it with the next run if that one follows directly with
the same value. -/
def mergeCons [DecidableEq α] (x : Run α) : Raw α → Raw α
  | [] => [x]
  | y :: rs =>
    if y.gap = 0 ∧ x.val = y.val then ⟨x.gap, x.len1 + y.len1 + 1, x.val⟩ :: rs
    else x :: y :: rs

/-- Merge adjacent runs with equal values. -/
def normalize [DecidableEq α] : Raw α → Raw α
  | [] => []
  | x :: rs => mergeCons x (normalize rs)

/-- `catMerge r n s` is `r` below `n` and `s` shifted to start at `n` (meaningful
when `r` maps no key at or above `n`), merging each run of `r` with its successor
where they are adjacent with equal values: the result is canonical whenever `s`
is. -/
def catMerge [DecidableEq α] : Raw α → Nat → Raw α → Raw α
  | [], n, s => addGap n s
  | ⟨g, l, v⟩ :: rs, n, s => mergeCons ⟨g, l, v⟩ (catMerge rs (n - (g + l + 1)) s)

/-- Map the keys `[lo, lo + len1]` to `v`. Canonical on canonical input; the runs
above `lo + len1` are shared, not rebuilt. -/
def assign [DecidableEq α] (r : Raw α) (lo len1 : Nat) (v : α) : Raw α :=
  catMerge (takeBelow r lo) lo (mergeCons ⟨0, len1, v⟩ (dropBelow r (lo + len1 + 1)))

/-- Unmap the keys `[lo, lo + len1]`. Canonical on canonical input. -/
def erase [DecidableEq α] (r : Raw α) (lo len1 : Nat) : Raw α :=
  catMerge (takeBelow r lo) (lo + len1 + 1) (dropBelow r (lo + len1 + 1))

/-- Assign the entries `(lo, len1, val)` (keys `[lo, lo + len1]`) from last to
first, so earlier entries take precedence. Each assignment costs O(1) when the
entries are disjoint and in increasing order. -/
def ofList [DecidableEq α] : List (Nat × Nat × α) → Raw α
  | [] => []
  | (lo, len1, v) :: l => assign (ofList l) lo len1 v

/-- The run list of `f` restricted to keys below `n`, assigned key by key. -/
def ofFn [DecidableEq α] (f : Nat → Option α) : Nat → Raw α
  | 0 => []
  | n + 1 =>
    match f n with
    | none => ofFn f n
    | some v => assign (ofFn f n) n 0 v

/-- The runs in absolute coordinates `(lo, len1, val)` (keys `[lo, lo + len1]`),
reading from base `b`. -/
def toListFrom : Nat → Raw α → List (Nat × Nat × α)
  | _, [] => []
  | b, ⟨g, l, v⟩ :: rs => (b + g, l, v) :: toListFrom (b + g + l + 1) rs

/-- The runs in absolute coordinates `(lo, len1, val)` (keys `[lo, lo + len1]`). -/
def toList (r : Raw α) : List (Nat × Nat × α) := toListFrom 0 r

end Raw

end Silmaril.Data.NatRangeMap
