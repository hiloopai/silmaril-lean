module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.RegisterAllocation

/-! # Exercise sheet 2, question 3 (register allocation)

Source: `cam-optcomp-2025-exercise-sheet-2` in `references.bib`, question 3.


(a) Register allocation maps the unboundedly many virtual registers of normal
form onto the machine's few registers. Variables that never clash can share a
register, so a `k`-colouring of the clash graph is an allocation into `k`
registers: `Flowgraph.rename_correct` (notes p. 10), found heuristically by
`chaitin` (notes p. 11).

(b) Building the clash graph and colouring it costs time quadratic in the
number of variables (graph colouring itself is NP-complete); a JIT pays this at
run time, on every compilation.

(c) *Linear scan* (Poletto & Sarkar, TOPLAS 1999) approximates each variable's
liveness by one interval of instruction positions, sorts the intervals by start
point, and allocates registers greedily in one pass, freeing a register when
its interval ends. It runs in near-linear time but is less precise: intervals
over-approximate live ranges with holes. `linearScan_valid`: whenever it
succeeds without spilling, overlapping intervals get different registers.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S2Q3

/-- A live interval `[start, stop]` of a variable. -/
structure Interval (V : Type*) where
  var : V
  start : ℕ
  stop : ℕ

variable {V : Type*} [DecidableEq V]

/-- Intervals overlap. -/
def Interval.Overlaps (a b : Interval V) : Prop := a.start ≤ b.stop ∧ b.start ≤ a.stop

/-- Linear scan over intervals sorted by start: `active` holds the allocated
intervals whose registers are still in use; each new interval expires the
active ones that ended before it starts, then takes the least free register.
Returns the assignment, or `none` if a spill would be needed. -/
def linearScan (k : ℕ) : List (Interval V) → List (Interval V × Fin k) → Option (List (Interval V × Fin k))
  | [], acc => some acc
  | i :: is, acc =>
    let active := acc.filter fun p => decide (i.start ≤ p.1.stop)
    match (List.finRange k).find? fun r => !(active.any fun p => decide (p.2 = r)) with
    | some r => linearScan k is ((i, r) :: acc)
    | none => none

omit [DecidableEq V] in
/-- The invariant of linear scan, for any accumulator. Sortedness is not
needed: an interval is only compared against the allocated intervals that
are still active at its start, and every overlapping one is. -/
theorem linearScan_aux {k : ℕ} : ∀ (is : List (Interval V)) (acc res : List (Interval V × Fin k)),
    (∀ p ∈ acc, ∀ q ∈ acc, p ≠ q → p.1.Overlaps q.1 → p.2 ≠ q.2) →
    linearScan k is acc = some res →
    res.map Prod.fst = is.reverse ++ acc.map Prod.fst ∧
      ∀ p ∈ res, ∀ q ∈ res, p ≠ q → p.1.Overlaps q.1 → p.2 ≠ q.2
  | [], acc, res, hv, h => by
    simp only [linearScan, Option.some.injEq] at h
    subst h
    exact ⟨by simp, hv⟩
  | i :: is, acc, res, hv, h => by
    simp only [linearScan] at h
    split at h
    next r hr =>
      have hfree := List.find?_some hr
      beta_reduce at hfree
      have key : ∀ p ∈ acc, p.1.Overlaps i → p.2 ≠ r := by
        intro p hp hov heq
        have hmem : p ∈ acc.filter (fun p => decide (i.start ≤ p.1.stop)) :=
          List.mem_filter.2 ⟨hp, by simpa using hov.2⟩
        have hany : (acc.filter fun p => decide (i.start ≤ p.1.stop)).any
            (fun p => decide (p.2 = r)) = true :=
          List.any_eq_true.2 ⟨p, hmem, by simpa using heq⟩
        rw [hany] at hfree
        exact absurd hfree (by decide)
      have hv' : ∀ p ∈ (i, r) :: acc, ∀ q ∈ (i, r) :: acc, p ≠ q → p.1.Overlaps q.1 →
          p.2 ≠ q.2 := by
        intro p hp q hq hpq hov
        rcases List.mem_cons.1 hp with rfl | hp₁ <;> rcases List.mem_cons.1 hq with rfl | hq₁
        · exact absurd rfl hpq
        · exact (key q hq₁ ⟨hov.2, hov.1⟩).symm
        · exact key p hp₁ hov
        · exact hv p hp₁ q hq₁ hpq hov
      obtain ⟨h1, h2⟩ := linearScan_aux is ((i, r) :: acc) res hv' h
      exact ⟨by simp [h1], h2⟩
    next => simp at h

omit [DecidableEq V] in
/-- Linear scan is valid: when it succeeds on intervals sorted by start, it
assigns every interval once, and overlapping intervals get different
registers. -/
theorem linearScan_valid {k : ℕ} {is : List (Interval V)}
    (hsorted : is.Pairwise fun a b => a.start ≤ b.start) {res : List (Interval V × Fin k)}
    (h : linearScan k is [] = some res) :
    res.map Prod.fst = is.reverse ∧
      ∀ p ∈ res, ∀ q ∈ res, p ≠ q → p.1.Overlaps q.1 → p.2 ≠ q.2 := by
  have _ := hsorted
  obtain ⟨h1, h2⟩ := linearScan_aux is [] res (by simp) h
  exact ⟨by simpa using h1, h2⟩

end Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S2Q3
