module

public import Mathlib.Data.List.Basic

/-!
# Locating the first disagreement in a proposal

Two one-line utilities shared by the checkers of `Machine/Lift`. Both exist so
that a rejection can name *where* a proposal went wrong rather than only that it
did: a checker that reports `mismatch` and nothing else cannot be acted on by
the agent that produced the proposal.

Neither is defined by well-founded recursion, so both reduce in the kernel and a
`decide` on a checker that calls them goes through.
-/

@[expose] public section

namespace Silmaril.Machine.Lift

variable {α : Type}

/-- The first index at which two lists differ, taking a list that runs out
early to differ at its own length. -/
def firstDiff [DecidableEq α] : Nat → List α → List α → Option Nat
  | _, [], [] => none
  | i, x :: xs, y :: ys => if x = y then firstDiff (i + 1) xs ys else some i
  | i, _, _ => some i

/-- Two lists with no first difference are equal. -/
theorem eq_of_firstDiff_none [DecidableEq α] :
    ∀ (i : Nat) (xs ys : List α), firstDiff i xs ys = none → xs = ys := by
  intro i xs
  induction xs generalizing i with
  | nil => intro ys h; cases ys with
    | nil => rfl
    | cons y ys => simp [firstDiff] at h
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => simp [firstDiff] at h
    | cons y ys =>
      simp only [firstDiff] at h
      split at h
      · rename_i hxy; exact hxy ▸ congrArg _ (ih (i + 1) ys h)
      · exact absurd h (by simp)

/-- The indices of the first pair of equal entries of a list, if it has one. -/
def firstDuplicate [DecidableEq α] : List α → Option (Nat × Nat) :=
  let rec go (i : Nat) : List α → Option (Nat × Nat)
    | [] => none
    | x :: rest =>
      match rest.idxOf? x with
      | some j => some (i, i + j + 1)
      | none => go (i + 1) rest
  go 0

/-- A list with no first duplicate has no duplicates. -/
theorem nodup_of_firstDuplicate_none [DecidableEq α] :
    ∀ (i : Nat) (xs : List α), firstDuplicate.go i xs = none → xs.Nodup := by
  intro i xs
  induction xs generalizing i with
  | nil => intro _; exact List.nodup_nil
  | cons x xs ih =>
    intro h
    simp only [firstDuplicate.go] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hidx
      refine List.nodup_cons.mpr ⟨?_, ih (i + 1) h⟩
      intro hx
      exact absurd hidx (by simp [List.idxOf?_eq_none_iff, hx])

end Silmaril.Machine.Lift
