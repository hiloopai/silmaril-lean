module

public import Silmaril.Semantics.Accept.Defs
public import Mathlib.Order.Basic

/-!
# Bounded domains and checkers correct on a domain

A specification `L : Set α` is often checked only on a *domain* `D : Set α` of inputs, for
example the inputs of length at most `n`, or the documents of nesting depth at most `d`. This
file fixes the generic vocabulary; the measures (byte length, item length, nesting depth of a
format, …) are supplied by each format.

* `within μ b`: the inputs whose measure `μ a : β` is at most `b`, for a measure into any
  preorder. Length bounds (`μ = List.length`), format-depth bounds (`μ = depth`) and combined
  bounds (`μ = fun a => (length a, depth a)` into the product order) are all instances.
* `SoundOn D check L`, `CompleteOn D check L`, `DecidesOn D check L`: soundness, completeness
  and decision *relative to* `D`; on `D = Set.univ` they are the unrelativised notions of
  `Silmaril.Semantics.Accept.Defs` (`Thms`).

## Bounded completeness is a choice, not a law

Nothing here asserts that completeness must be bounded. Whether a checker is complete on all
of `α` or only on a bounded domain depends on the setting:

* a *one-shot* interface that takes the whole input in a fixed buffer (for example a
  call across a Wasm ABI with a bounded memory) can only be complete on inputs that fit;
* a *streaming* checker that consumes input incrementally can be complete on inputs of
  unbounded total size, possibly with a bound on each item only;
* a *semantic* specification (a `Set α`) needs no bound at all, while an *executable* total
  decision procedure may need one for resources, or may have none (a total `α → Bool` that
  `Decides` the whole language).

The laws in `Thms` cover both readings: completeness on every bounded domain of an exhaustive
family is completeness everywhere (`completeOn_univ_of_forall_within`), and a checker that is
complete on a large domain is complete on every smaller one.
-/

@[expose] public section

namespace Silmaril.Accept

universe u v

variable {α : Type u} {β : Type v}

/-- The inputs whose measure is at most `b`. -/
def within [LE β] (μ : α → β) (b : β) : Set α := {a | μ a ≤ b}

/-- `check` is sound for `L` on `D`: whatever it accepts in `D` lies in `L`. -/
def SoundOn (D : Set α) (check : α → Bool) (L : Set α) : Prop :=
  ∀ a ∈ D, check a = true → a ∈ L

/-- `check` is complete for `L` on `D`: it accepts every member of `L` in `D`. -/
def CompleteOn (D : Set α) (check : α → Bool) (L : Set α) : Prop :=
  ∀ a ∈ D, a ∈ L → check a = true

/-- `check` decides `L` on `D`: on inputs in `D` it accepts exactly the members of `L`.
Outside `D` it may answer anything. -/
def DecidesOn (D : Set α) (check : α → Bool) (L : Set α) : Prop :=
  ∀ a ∈ D, (check a = true ↔ a ∈ L)

end Silmaril.Accept
