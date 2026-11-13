module

public import Silmaril.Proofs.Logic.SAT.LRAT.Rat

@[expose] public section

/-!
# A reference LRAT checker: examples

* `fourClauses`: all four clauses over two variables, refuted by a two-step RUP proof;
* `php32`: the pigeonhole formula PHP(3, 2) (three pigeons, two holes), refuted by a three-step
  RUP proof with a deletion;
* `satTwo`: a satisfiable formula, with bogus proofs that `check` rejects;
* `zeroUnit`: the satisfiable `[[0]]`, whose would-be refutation by the unit `0` is rejected;
* RAT: `fourClausesRatProof` adds the unit `[3]` of a fresh variable (a RAT step with no
  candidate, which no hint list justifies by RUP: `fresh_not_rup`) and `[-3, 1]` (a RAT step
  with one candidate), then refutes `fourClauses` through them; bogus RAT steps are rejected
  (`rat_bogus_rejected`).
-/

namespace Silmaril.Logic.SAT.LRAT

/-- `(x₁ ∨ x₂) ∧ (¬x₁ ∨ x₂) ∧ (x₁ ∨ ¬x₂) ∧ (¬x₁ ∨ ¬x₂)`. -/
def fourClauses : CNF := [[1, 2], [-1, 2], [1, -2], [-1, -2]]

/-- Clause 5 `x₂` by RUP along 1, 2; then the empty clause along 5, 3, 4. -/
def fourClausesProof : List Step := [.add 5 [2] [1, 2], .add 6 [] [5, 3, 4]]

theorem fourClauses_check : check fourClauses fourClausesProof = true := by decide

theorem fourClauses_unsat : fourClauses.Unsat := check_sound fourClauses_check

/-- PHP(3, 2): pigeon `i ∈ {1, 2, 3}` in hole `j ∈ {1, 2}` is variable `2 (i - 1) + j`. Clauses
1–3: every pigeon has a hole; 4–6: hole 1 holds at most one pigeon; 7–9: hole 2 likewise. -/
def php32 : CNF :=
  [[1, 2], [3, 4], [5, 6], [-1, -3], [-1, -5], [-3, -5], [-2, -4], [-2, -6], [-4, -6]]

/-- Pigeon 1 is in neither hole (clauses 10, 11); the hole clauses are then deleted, and clause 1
gives the conflict. -/
def php32Proof : List Step :=
  [.add 10 [-1] [4, 5, 2, 3, 9], .add 11 [-2] [7, 8, 2, 3, 6], .del [4, 5, 6, 7, 8, 9],
    .add 12 [] [10, 11, 1]]

theorem php32_check : check php32 php32Proof = true := by decide

theorem php32_unsat : php32.Unsat := check_sound php32_check

/-- `(x₁ ∨ x₂) ∧ (¬x₁ ∨ x₂)`, satisfied by making every variable true. -/
def satTwo : CNF := [[1, 2], [-1, 2]]

theorem satTwo_sat : satTwo.Sat := ⟨fun _ => true, by decide⟩

/-- Bogus proofs are rejected: a non-unit hint, exhausted hints, a missing id, a valid proof that
never adds the empty clause, a hint used after its deletion, and the empty proof. -/
theorem satTwo_bogus_rejected :
    check satTwo [.add 3 [] [1, 2]] = false ∧ check satTwo [.add 3 [2] [1]] = false ∧
      check satTwo [.add 3 [] [7]] = false ∧ check satTwo [.add 3 [2] [1, 2]] = false ∧
      check satTwo [.add 3 [2] [1, 2], .del [3], .add 4 [] [3]] = false ∧
      check satTwo [] = false := by
  decide

/-- The satisfiable `[[0]]` (true when variable `0` is false). -/
def zeroUnit : CNF := [[0]]

theorem zeroUnit_sat : zeroUnit.Sat := ⟨fun _ => false, by decide⟩

/-- Propagating the unit `0` twice would give a conflict (`-0 = 0`), so it is rejected; so is a
clause containing `0`. -/
theorem zeroUnit_rejected :
    check zeroUnit [.add 2 [] [1, 1]] = false ∧ check zeroUnit [.add 2 [0] [1], .add 3 [] [2, 2]] = false := by
  decide

/-! ## RAT steps -/

/-- Clause 5 `[3]` by RAT on the fresh variable `3` (no clause contains `-3`); clause 6
`[-3, 1]` by RAT on `-3` (the only candidate, clause 5, gives the resolvent `[-3, 1]`, refuted
along clauses 1, 3); clause 7 `[1]` by RUP along 5, 6; the empty clause along 7, 2, 4. -/
def fourClausesRatProof : List Step :=
  [.rat 5 [3] [], .rat 6 [-3, 1] [(5, [1, 3])], .add 7 [1] [5, 6], .add 8 [] [7, 2, 4]]

theorem fourClausesRat_check : check fourClauses fourClausesRatProof = true := by decide

theorem fourClausesRat_unsat : fourClauses.Unsat := check_sound fourClausesRat_check

/-- The first step needs RAT: from the input database no hint list justifies `[3]` by RUP
(every input clause keeps both of its literals under the assumption `-3`). -/
theorem fresh_not_rup (hs : List Nat) : addOk (init 1 fourClauses) [3] hs = false := by
  cases hs with
  | nil => rfl
  | cons h hs =>
    have hl : lookup (init 1 fourClauses) h = none ∨
        ∃ D ∈ fourClauses, lookup (init 1 fourClauses) h = some D := by
      simp only [fourClauses, init, lookup, beq_iff_eq]
      repeat' split
      all_goals simp
    rcases hl with hl | ⟨D, hD, hl⟩
    · simp [addOk, rup, hl]
    · simp only [fourClauses, List.mem_cons, List.not_mem_nil, or_false] at hD
      rcases hD with rfl | rfl | rfl | rfl <;> simp [addOk, rup, hl, unfalsified]

/-- Bogus RAT steps are rejected: an uncovered candidate (`[-2]` on `satTwo`, whose clauses 1
and 2 contain `2`), a group naming the wrong id, a group whose hints do not refute the
resolvent, an empty RAT clause, and a pivot `0`. -/
theorem rat_bogus_rejected :
    check satTwo [.rat 3 [-2] [], .add 4 [] [1, 2, 3]] = false ∧
      check satTwo [.rat 3 [-2] [(1, [1]), (7, [2])], .add 4 [] [1, 2, 3]] = false ∧
      check satTwo [.rat 3 [-2] [(1, [2]), (2, [1])], .add 4 [] [1, 2, 3]] = false ∧
      check satTwo [.rat 3 [] []] = false ∧ check satTwo [.rat 3 [0] [], .add 4 [] [3]] = false := by
  decide

end Silmaril.Logic.SAT.LRAT
