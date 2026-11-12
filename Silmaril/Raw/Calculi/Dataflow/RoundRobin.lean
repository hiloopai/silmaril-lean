module

public import Silmaril.Semantics.Dataflow.Iteration
public import Mathlib.Data.List.FinRange

/-! # Round-robin (Gauss–Seidel) iteration

The algorithm of Optimising Compilers §2, p. 9, updates `live[i]` in place for
`i = 1, …, N` and repeats while anything changes:

```
for i=1 to N do live[i] := {}
while (live[] changes) do
  for i=1 to N do live[i] := (⋃ s ∈ succ(i), live[s]) \ def(i) ∪ ref(i)
```

`roundRobinPass` is one sweep of the inner loop. Each sweep stays below the
least solution and above the Jacobi iterate, so the sweeps reach the least
solution, and a sweep that changes nothing has reached it.
-/

@[expose] public section

open Silmaril.Semantics.Dataflow

namespace Silmaril.Calculi.Dataflow

namespace Equations

variable {N : ℕ} {L : Type*} [CompleteLattice L] (E : Equations (Fin N) L)

/-- One in-place sweep `for i = 1 to N do x[i] := transfer i (join x i)`. -/
def roundRobinPass (x : Fin N → L) : Fin N → L :=
  (List.finRange N).foldl (fun y i => Function.update y i (E.transfer i (E.join y i))) x

/-- One in-place update `x[i] := transfer i (join x i)`. -/
def rrUpdate (y : Fin N → L) (i : Fin N) : Fin N → L :=
  Function.update y i (E.transfer i (E.join y i))

theorem roundRobinPass_eq_foldl (x : Fin N → L) :
    (roundRobinPass E) x = (List.finRange N).foldl (rrUpdate E) x := rfl

/-- An in-place update of a pre-fixed point (`z ≤ step z`) increases it and
stays a pre-fixed point. -/
theorem le_rrUpdate {z : Fin N → L} (hz : z ≤ E.step z) (j : Fin N) :
    z ≤ (rrUpdate E) z j ∧ (rrUpdate E) z j ≤ E.step ((rrUpdate E) z j) := by
  have hle : z ≤ (rrUpdate E) z j := by
    intro i
    by_cases h : i = j
    · rw [h, rrUpdate, Function.update_self]
      exact hz j
    · rw [rrUpdate, Function.update_of_ne h]
  refine ⟨hle, fun i => ?_⟩
  by_cases h : i = j
  · rw [h, rrUpdate, Function.update_self]
    exact E.step.monotone hle j
  · rw [rrUpdate, Function.update_of_ne h]
    exact (hz i).trans (E.step.monotone hle i)

/-- A sequence of in-place updates from a pre-fixed point increases it, stays a
pre-fixed point, and dominates one Jacobi round at every updated node. -/
theorem foldl_rrUpdate (l : List (Fin N)) {z : Fin N → L} (hz : z ≤ E.step z) :
    z ≤ l.foldl (rrUpdate E) z ∧ l.foldl (rrUpdate E) z ≤ E.step (l.foldl (rrUpdate E) z) ∧
      ∀ j ∈ l, E.step z j ≤ l.foldl (rrUpdate E) z j := by
  induction l generalizing z with
  | nil => exact ⟨le_rfl, hz, fun j hj => by simp at hj⟩
  | cons j l ih =>
    obtain ⟨h1, h2⟩ := (le_rrUpdate E) hz j
    obtain ⟨h3, h4, h5⟩ := ih h2
    refine ⟨h1.trans h3, h4, fun i hi => ?_⟩
    rcases List.mem_cons.1 hi with h | hi
    · have : E.step z j = (rrUpdate E) z j j := by simp [rrUpdate, Silmaril.Semantics.Dataflow.Equations.step_apply]
      rw [h, this]
      exact h3 j
    · exact (E.step.monotone h1 i).trans (h5 i hi)

/-- Sweeps from below the least solution stay below it. -/
theorem roundRobinPass_le_least {x : Fin N → L} (hx : x ≤ E.least) :
    (roundRobinPass E) x ≤ E.least := by
  rw [roundRobinPass_eq_foldl]
  generalize List.finRange N = l
  induction l generalizing x with
  | nil => exact hx
  | cons j l ih =>
    apply ih
    intro i
    by_cases h : i = j
    · rw [h, rrUpdate, Function.update_self]
      calc E.transfer j (E.join x j) ≤ E.transfer j (E.join E.least j) :=
            (E.transfer j).monotone (E.join_mono hx j)
        _ = E.least j := congrFun E.least_isSolution j
    · rw [rrUpdate, Function.update_of_ne h]
      exact hx i

/-- A sweep dominates one Jacobi round from a value below its result. -/
theorem step_le_roundRobinPass {x : Fin N → L} (hx : x ≤ E.step x) :
    E.step x ≤ (roundRobinPass E) x := fun j =>
  ((foldl_rrUpdate E) (List.finRange N) hx).2.2 j (List.mem_finRange j)

/-- The sweeps from `⊥` are pre-fixed points. -/
theorem iterate_roundRobinPass_le_step (k : ℕ) :
    (roundRobinPass E)^[k] ⊥ ≤ E.step ((roundRobinPass E)^[k] ⊥) := by
  induction k with
  | zero => exact bot_le
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ((foldl_rrUpdate E) (List.finRange N) ih).2.1

/-- The sweeps from `⊥` increase. -/
theorem monotone_iterate_roundRobinPass : Monotone fun k => (roundRobinPass E)^[k] ⊥ :=
  monotone_nat_of_le_succ fun k => by
    rw [Function.iterate_succ_apply']
    exact ((foldl_rrUpdate E) (List.finRange N) ((iterate_roundRobinPass_le_step E) k)).1

/-- The sweeps from `⊥` stay below the least solution. -/
theorem iterate_roundRobinPass_le_least (k : ℕ) : (roundRobinPass E)^[k] ⊥ ≤ E.least := by
  induction k with
  | zero => exact bot_le
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (roundRobinPass_le_least E) ih

/-- A sweep that changes nothing, started from `⊥` and iterated, is at the
least solution. -/
theorem roundRobin_eq_least_of_stable {k : ℕ}
    (h : (roundRobinPass E) ((roundRobinPass E)^[k] ⊥) = (roundRobinPass E)^[k] ⊥) :
    (roundRobinPass E)^[k] ⊥ = E.least :=
  le_antisymm ((iterate_roundRobinPass_le_least E) k) <| E.least_le_of_isSafe <|
    ((step_le_roundRobinPass E) ((iterate_roundRobinPass_le_step E) k)).trans_eq h

/-- On lattices of finite height the sweeps reach the least solution. -/
theorem exists_roundRobin_eq_least [WellFoundedGT (Fin N → L)] :
    ∃ k, (roundRobinPass E)^[k] ⊥ = E.least := by
  obtain ⟨n, hn⟩ := wellFoundedGT_iff_monotone_chain_condition.1 ‹WellFoundedGT (Fin N → L)›
    ⟨fun k => (roundRobinPass E)^[k] ⊥, (monotone_iterate_roundRobinPass E)⟩
  refine ⟨n, (roundRobin_eq_least_of_stable E) ?_⟩
  have h : (roundRobinPass E)^[n] ⊥ = (roundRobinPass E)^[n + 1] ⊥ := hn (n + 1) (Nat.le_succ n)
  rw [Function.iterate_succ_apply'] at h
  exact h.symm

end Equations

end Silmaril.Calculi.Dataflow
