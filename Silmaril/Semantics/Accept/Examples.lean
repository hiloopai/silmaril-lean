module

public import Silmaril.Semantics.Accept.Thms

/-! # Acceptance: worked examples and regression tests

Small instances of `Silmaril.Semantics.Accept`: a checker for even numbers, a Bool connective,
a nondeterministic runner whose existential and universal verdicts differ, and a size slice.
Every `example` is checked when the library builds.
-/

@[expose] public section

namespace Silmaril.Accept.Examples

open Silmaril.Accept

/-! ## A Bool checker -/

/-- The even naturals. -/
def evens : Set ℕ := {n | n % 2 = 0}

/-- A checker for `evens`. -/
def isEven (n : ℕ) : Bool := n % 2 == 0

theorem isEven_decides : Decides isEven evens := fun n => by simp [isEven, evens]

example : isEven 4 = true := by decide
example : (3 : ℕ) ∉ evens := by simp [evens]
example : Sound isEven evens := isEven_decides.sound
example : ofBool isEven = evens := decides_iff_ofBool_eq.1 isEven_decides

/-- Connectives: `isEven n && n ≤ 10` decides the even numbers up to `10`. -/
example : Decides (fun n => isEven n && decide (n ≤ 10)) (upTo id 10 evens) :=
  isEven_decides.upTo id 10

instance : DecidablePred (· ∈ evens) := fun n => inferInstanceAs (Decidable (n % 2 = 0))

/-- The canonical checker of a decidable set decides it. -/
example : Decides (checker evens) evens := decides_checker evens

/-! ## Existential acceptance against universal never-rejection

Outcomes are `true` (accept) and `false` (reject). Input `0` has both outcomes, input `1` only
accepts, input `2` has no outcome (it diverges).
-/

/-- A nondeterministic runner on three inputs. -/
def run : Fin 3 → Set Bool
  | 0 => {true, false}
  | 1 => {true}
  | 2 => ∅

/-- Some run of `0` accepts, but `0` can also reject. -/
example : (0 : Fin 3) ∈ acceptsSome run {true} := ⟨true, by simp [run]⟩
example : (0 : Fin 3) ∉ neverRejects run {false} := fun h => h false (by simp [run]) rfl

/-- The diverging input never rejects but is not accepted. -/
example : (2 : Fin 3) ∈ neverRejects run {false} := mem_neverRejects_of_eq_empty rfl
example : (2 : Fin 3) ∉ acceptsSome run {true} := not_mem_acceptsSome_of_eq_empty rfl
example : ¬ neverRejects run {false} ⊆ acceptsSome run {true} :=
  neverRejects_not_subset_acceptsSome (a := 2) rfl

/-- `1` is accepted on every run, hence never rejected. -/
example : (1 : Fin 3) ∈ neverRejects run {false} :=
  acceptsAll_subset_neverRejects (acc := {true}) (by simp) (by simp [run])

/-! ## Deterministic runners collapse the quantifiers -/

example : acceptsSome (detRun isEven) {true} = acceptsAll (detRun isEven) {true} := by
  rw [acceptsSome_detRun, acceptsAll_detRun]

/-! ## Size slices -/

example : (4 : ℕ) ∈ upTo id 5 evens := ⟨by simp [evens], by decide⟩
example : (6 : ℕ) ∉ upTo id 5 evens := fun h => absurd h.2 (by decide)
example : ⋃ n, upTo id n evens = evens := iUnion_upTo

end Silmaril.Accept.Examples
