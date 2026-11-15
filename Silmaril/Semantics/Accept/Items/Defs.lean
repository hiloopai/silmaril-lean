module

public import Silmaril.Semantics.Accept.Bounded.Defs
public import Cslib.Foundations.Data.OmegaSequence.Defs
public import Mathlib.Computability.Language

/-!
# Item sequences: per-item bounds and whole-sequence bounds

Line-delimited formats such as JSON Lines are sequences of *items*. A bound on each item is
a different thing from a bound on the whole sequence. This file is generic over the item type
`ι` and the measures; concrete validity (what a JSON text is, which bytes separate lines)
belongs to the format developments.

Two kinds of sequence are kept apart by name:

* **finite item lists** `List ι`: finitely many items, but arbitrarily many;
* **infinite item sequences** `ωSequence ι` (CSLib), suffixed `ω`: an unending stream, as in
  `Silmaril.Semantics.Streams`.

## Definitions

* `everyItem L`: finite lists all of whose items lie in `L`.
* `itemsWithin μ n`: every item has measure at most `n` (per-item bound, for example the
  length of each line).
* `totalWithin w n`: the weights of all items sum to at most `n` (whole-list bound, for
  example the length of the whole file, with `w` counting an item and its separator).
* `countWithin n`: at most `n` items.
* `everyItemω L`, `itemsWithinω μ n`: the infinite counterparts. An infinite sequence has no
  finite total size, so only per-item bounds have an `ω` version.

A per-item bound does not bound the whole list (`Thms`): checkers correct on per-item bounded
domains are correct on lists of every total size.
-/

@[expose] public section

namespace Silmaril.Accept

universe u

variable {ι : Type u}

/-- Finite item lists all of whose items lie in `L`. -/
def everyItem (L : Set ι) : Set (List ι) := {s | ∀ x ∈ s, x ∈ L}

/-- Finite item lists each of whose items has measure at most `n`. -/
def itemsWithin (μ : ι → ℕ) (n : ℕ) : Set (List ι) := everyItem (within μ n)

/-- The total weight of a finite item list. -/
def totalWeight (w : ι → ℕ) (s : List ι) : ℕ := (s.map w).sum

/-- Finite item lists of total weight at most `n`. -/
def totalWithin (w : ι → ℕ) (n : ℕ) : Set (List ι) := within (totalWeight w) n

/-- Finite item lists of at most `n` items. -/
def countWithin (n : ℕ) : Set (List ι) := within List.length n

/-- Infinite item sequences all of whose items lie in `L`. -/
def everyItemω (L : Set ι) : Set (Cslib.ωSequence ι) := {s | ∀ k, s k ∈ L}

/-- Infinite item sequences each of whose items has measure at most `n`. -/
def itemsWithinω (μ : ι → ℕ) (n : ℕ) : Set (Cslib.ωSequence ι) := everyItemω (within μ n)

end Silmaril.Accept
