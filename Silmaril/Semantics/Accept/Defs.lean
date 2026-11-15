module

public import Mathlib.Data.Set.Lattice.Indexed

/-!
# Acceptance: languages as sets, Bool checkers, outcome quantifiers

A *language* over a carrier `α` is a `Set α` (Mathlib's `Set`, no new wrapper). This file fixes
the generic vocabulary used to say that a program, a checker or a nondeterministic runner
*accepts* a language. Nothing here is specific to any instruction set or format; WebAssembly,
WIT or byte-level developments instantiate these definitions.

## Bool checkers

A checker is a function `check : α → Bool`.

* `Accept.ofBool check`: the language `{a | check a = true}` the checker accepts.
* `Accept.Sound check L`: every accepted value lies in `L` (no false positives).
* `Accept.Complete check L`: every value of `L` is accepted (no false negatives).
* `Accept.Decides check L`: both; equivalently `ofBool check = L` (`Thms`).

## Outcome quantifiers

A nondeterministic runner is `run : α → Set ω`: the outcomes `ω` that input `a` can produce
(an empty set models an input with no completed run, such as divergence or a stuck
configuration). Given a set `acc` of accepting outcomes and a set `rej` of rejecting outcomes,
there are four different languages, and they are not interchangeable:

* `acceptsSome run acc`: *some* run accepts (existential, angelic acceptance).
* `acceptsAll run acc`: *every* run accepts (universal acceptance; vacuous for no runs).
* `rejectsSome run rej`: *some* run rejects.
* `neverRejects run rej`: *no* run rejects (universal safety); the complement of
  `rejectsSome`, *not* of `acceptsSome`.

When `run` is deterministic and total (`run a = {f a}`) all of them collapse to preimages
(`Thms`). For runners with no outcome, `acceptsSome` fails while `acceptsAll` and
`neverRejects` hold: never-rejection is weaker than acceptance.

## Size filters

* `Accept.upTo size n L`: the members of `L` of size at most `n`. Bounded enumeration and
  bounded testing reason about these finite slices; `⋃ n, upTo size n L = L` (`Thms`).
-/

@[expose] public section

namespace Silmaril.Accept

universe u v

variable {α : Type u} {ω : Type v}

/-! ## Bool checkers -/

/-- The language a Bool checker accepts. -/
def ofBool (check : α → Bool) : Set α := {a | check a = true}

/-- `check` is sound for `L`: whatever it accepts lies in `L`. -/
def Sound (check : α → Bool) (L : Set α) : Prop := ∀ a, check a = true → a ∈ L

/-- `check` is complete for `L`: it accepts every member of `L`. -/
def Complete (check : α → Bool) (L : Set α) : Prop := ∀ a, a ∈ L → check a = true

/-- `check` decides `L`: it accepts exactly the members of `L`. -/
def Decides (check : α → Bool) (L : Set α) : Prop := ∀ a, check a = true ↔ a ∈ L

/-- The canonical checker of a decidable language. -/
def checker (L : Set α) [DecidablePred (· ∈ L)] : α → Bool := fun a => decide (a ∈ L)

/-! ## Outcome quantifiers -/

/-- Existential acceptance: some outcome of `run a` is accepting. -/
def acceptsSome (run : α → Set ω) (acc : Set ω) : Set α := {a | ∃ o ∈ run a, o ∈ acc}

/-- Universal acceptance: every outcome of `run a` is accepting (vacuous with no outcome). -/
def acceptsAll (run : α → Set ω) (acc : Set ω) : Set α := {a | ∀ o ∈ run a, o ∈ acc}

/-- Some outcome of `run a` is rejecting. -/
def rejectsSome (run : α → Set ω) (rej : Set ω) : Set α := {a | ∃ o ∈ run a, o ∈ rej}

/-- Universal never-rejection: no outcome of `run a` is rejecting. -/
def neverRejects (run : α → Set ω) (rej : Set ω) : Set α := {a | ∀ o ∈ run a, o ∉ rej}

/-- The runner of a total deterministic function: exactly one outcome. -/
def detRun (f : α → ω) : α → Set ω := fun a => {f a}

/-! ## Size filters -/

/-- The members of `L` whose `size` is at most `n`. -/
def upTo (size : α → ℕ) (n : ℕ) (L : Set α) : Set α := {a | a ∈ L ∧ size a ≤ n}

end Silmaril.Accept
