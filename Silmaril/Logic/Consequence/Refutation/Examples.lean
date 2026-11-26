module

public import Silmaril.Logic.Consequence.Refutation.CNF.Thms
import Silmaril.Logic.SAT.CNF.Thms

/-!
# Examples: entailment by refutation

* **Clauses.** `[1, -1, 2]` is a tautology (`decide` on the complementary-pair test), hence
  entailed by `[]`; `[1, 2]` is not. Premises are read as sets: the CNF `[[1], [-1]]` is UNSAT,
  and so is any list with the same clauses, in any order or multiplicity (`unsat_of_subset`).
  Unit propagation `[[1], [-1, 2]] ⊨ [2]` is the UNSAT of `[[1], [-1, 2], [-2]]`.
* **A sound, incomplete checker is not cut-closed.** On literals `Bool × Nat`, `bounded k`
  accepts lists of length at most `k` containing a complementary pair. It is sound and the
  negation is exact, so `viaUnsat (bounded 3)` only derives entailments (and so does its Tarski
  closure), yet it is not closed under multi-cut: `[p, r] ⊢ p`, `[q] ⊢ q` and `[p, q] ⊢ p`
  hold but `[p, r, q] ⊢ p` does not.
-/

@[expose] public section

namespace Silmaril.Consequence.Refutation.Examples

open Silmaril.Logic.SAT Silmaril.Consequence.Structural CNF

/-! ## Clauses -/

/-- The clause `l₁ ∨ … ∨ lₙ` without the literal `0`. -/
abbrev cl (C : Clause) (h : (0 : Lit) ∉ C := by decide) : WClause := ⟨C, h⟩

theorem tauto_1_n1_2 : Tauto [1, -1, 2] := by decide

theorem entails_tauto : Entails csat [] (cl [1, -1, 2]) := (entails_nil_iff_tauto _).2 (by decide)

theorem not_entails_1_2 : ¬ Entails csat [] (cl [1, 2]) := fun h => absurd ((entails_nil_iff_tauto _).1 h)
  (by decide)

/-- Unsatisfiability depends only on which clauses occur. -/
theorem unsat_of_subset {M C : Type} {sat : M → C → Prop} {Γ Δ : List C} (h : Γ ⊆ Δ)
    (hΓ : Unsat sat Γ) : Unsat sat Δ :=
  fun m hm => hΓ m fun x hx => hm x (h hx)

theorem unsat_pair : Unsat csat [cl [1], cl [-1]] := by
  intro τ h
  have h1 := h (cl [1]) (by simp)
  have h2 := h (cl [-1]) (by simp)
  simp [csat, Clause.eval] at h1 h2
  rw [lit_eval_neg τ (by decide)] at h2
  simp_all

theorem unsat_dup : Unsat csat [cl [-1], cl [1], cl [-1], cl [1]] :=
  unsat_of_subset (by simp) unsat_pair

theorem cnf_unsat_pair : CNF.Unsat [[1], [-1]] := (unsat_iff [cl [1], cl [-1]]).1 unsat_pair

/-- Unit propagation, as an entailment. -/
theorem unit_prop : Entails csat [cl [1], cl [-1, 2]] (cl [2]) := by
  intro τ h
  have h1 := h (cl [1]) (by simp)
  have h2 := h (cl [-1, 2]) (by simp)
  simp [csat, Clause.eval] at h1 h2 ⊢
  rw [lit_eval_neg τ (by decide)] at h2
  simp_all

/-- The same entailment, as a CNF refutation. -/
theorem cnf_unit_prop : CNF.Unsat [[1], [-1, 2], [-2]] :=
  (entails_iff_cnf_unsat [cl [1], cl [-1, 2]] (cl [2])).1 unit_prop

/-! ## A sound, incomplete checker -/

/-- A literal: polarity and variable. -/
abbrev BLit := Bool × Nat

/-- An assignment satisfies a literal. -/
def bsat (τ : Nat → Bool) (l : BLit) : Prop := τ l.2 = l.1

/-- The negation of a literal, as a one-element list. -/
def bneg (l : BLit) : List BLit := [(!l.1, l.2)]

/-- Accepts lists of length at most `k` containing a complementary pair. -/
def bounded (k : Nat) (Γ : List BLit) : Prop := Γ.length ≤ k ∧ ∃ l ∈ Γ, (!l.1, l.2) ∈ Γ

instance (k : Nat) (Γ : List BLit) : Decidable (bounded k Γ) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem bneg_sound : NegSound bsat bneg := fun τ l h hl => by
  have := h _ (List.mem_singleton_self _); simp_all [bsat]

theorem bneg_complete : NegComplete bsat bneg := fun τ l h x hx => by
  simp only [bneg, List.mem_singleton] at hx; subst hx
  obtain ⟨b, v⟩ := l; cases hb : τ v <;> cases b <;> simp_all [bsat]

theorem bounded_sound (k : Nat) : CheckSound bsat (bounded k) := by
  rintro Γ ⟨-, l, hl, hn⟩ τ h
  have h1 := h _ hl; have h2 := h _ hn; simp_all [bsat]

/-- The checker's relation only derives entailments, even after closing it. -/
theorem bounded_closure_sound : Derives tarskiRules (viaUnsat (bounded 3) bneg) ≤ Entails bsat :=
  derives_viaUnsat_le_entails (bounded_sound 3) bneg_complete

/-- But it is not cut-closed. -/
theorem bounded_not_cut : ¬ Cut (viaUnsat (bounded 3) bneg) := by
  intro h
  let p : BLit := (true, 0)
  let q : BLit := (true, 1)
  let r : BLit := (true, 2)
  have := @h [([p, r], p), ([q], q)] p
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> (unfold viaUnsat; decide))
    (by unfold viaUnsat; decide)
  unfold viaUnsat at this; revert this; decide

/-- Yet the conclusion of that cut is an entailment. -/
theorem bounded_cut_conclusion_entailed : Entails bsat [(true, 0), (true, 2), (true, 1)] (true, 0) :=
  fun _ h => h _ (by simp)

end Silmaril.Consequence.Refutation.Examples
