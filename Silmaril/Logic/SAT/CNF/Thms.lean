module

public import Silmaril.Logic.SAT.CNF.Defs

@[expose] public section

/-!
# Propositional CNF formulas and DIMACS: basic facts

* evaluation of clauses and formulas over `++`, `::` and `[]`;
* implication: `CNF.Implies.of_mem`, `CNF.Implies.append` (more clauses imply more),
  `CNF.Unsat.of_implies_nil` (a formula implying the empty clause is unsatisfiable),
  `CNF.Unsat.append`;
* DIMACS streams: `Dimacs.read_snoc` (reading is a left fold), `Dimacs.cnf_snoc_zero`,
  `Dimacs.pending_snoc_zero`, `Dimacs.cnf_snoc_ne`, `Dimacs.pending_snoc_ne`, and
  `Dimacs.cnf_append` (later integers only add clauses).

A Silmaril addition.
-/

namespace Silmaril.Logic.SAT

@[simp] theorem Clause.eval_nil (τ : Assignment) : Clause.eval τ [] = false := rfl

@[simp] theorem Clause.eval_cons (τ : Assignment) (l : Lit) (C : Clause) :
    Clause.eval τ (l :: C) = (l.eval τ || Clause.eval τ C) := rfl

@[simp] theorem Clause.eval_append (τ : Assignment) (C D : Clause) :
    Clause.eval τ (C ++ D) = (Clause.eval τ C || Clause.eval τ D) := by
  simp [Clause.eval, List.any_append]

theorem Clause.eval_eq_true_iff (τ : Assignment) (C : Clause) :
    Clause.eval τ C = true ↔ ∃ l ∈ C, l.eval τ = true := by
  simp [Clause.eval]

theorem Clause.eval_eq_false_iff (τ : Assignment) (C : Clause) :
    Clause.eval τ C = false ↔ ∀ l ∈ C, l.eval τ = false := by
  simp [Clause.eval]

@[simp] theorem CNF.eval_nil (τ : Assignment) : CNF.eval τ [] = true := rfl

@[simp] theorem CNF.eval_append (τ : Assignment) (F G : CNF) :
    CNF.eval τ (F ++ G) = (CNF.eval τ F && CNF.eval τ G) := by
  simp [CNF.eval, List.all_append]

theorem CNF.eval_eq_true_iff (τ : Assignment) (F : CNF) :
    CNF.eval τ F = true ↔ ∀ C ∈ F, C.eval τ = true := by
  simp [CNF.eval]

theorem CNF.eval_of_append {τ : Assignment} {F G : CNF} (h : CNF.eval τ (F ++ G) = true) :
    CNF.eval τ F = true := by
  simp only [CNF.eval_append, Bool.and_eq_true] at h
  exact h.1

/-- A clause of a formula is implied by it. -/
theorem CNF.Implies.of_mem {F : CNF} {C : Clause} (h : C ∈ F) : F.Implies C :=
  fun τ hτ => (CNF.eval_eq_true_iff τ F).1 hτ C h

/-- Adding clauses keeps implications. -/
theorem CNF.Implies.append {F : CNF} {C : Clause} (h : F.Implies C) (G : CNF) :
    (F ++ G).Implies C :=
  fun τ hτ => h τ (CNF.eval_of_append hτ)

/-- A formula implying the empty clause is unsatisfiable. -/
theorem CNF.Unsat.of_implies_nil {F : CNF} (h : F.Implies []) : F.Unsat := by
  intro τ
  cases hτ : CNF.eval τ F with
  | false => rfl
  | true => exact absurd (h τ hτ) (by simp)

/-- Adding clauses keeps unsatisfiability. -/
theorem CNF.Unsat.append {F : CNF} (h : F.Unsat) (G : CNF) : (F ++ G).Unsat := by
  intro τ
  simp [h τ]

theorem CNF.not_sat_of_unsat {F : CNF} (h : F.Unsat) : ¬ F.Sat := by
  rintro ⟨τ, hτ⟩
  rw [h τ] at hτ
  cases hτ

namespace Dimacs

/-- Reading a stream is a left fold of `step`. -/
theorem read_snoc (xs : List Int) (x : Int) : read (xs ++ [x]) = step (read xs) x := by
  simp [read, List.foldl_append]

theorem cnf_snoc_zero (xs : List Int) : cnf (xs ++ [0]) = cnf xs ++ [pending xs] := by
  simp [cnf, pending, read_snoc, step]

theorem pending_snoc_zero (xs : List Int) : pending (xs ++ [0]) = [] := by
  simp [pending, read_snoc, step]

theorem step_ne (F : CNF) (c : Clause) {x : Int} (hx : x ≠ 0) : step (F, c) x = (F, c ++ [x]) := by
  match x, hx with
  | .ofNat 0, h => exact absurd rfl h
  | .ofNat (_ + 1), _ => rfl
  | .negSucc _, _ => rfl

theorem cnf_snoc_ne (xs : List Int) {x : Int} (hx : x ≠ 0) : cnf (xs ++ [x]) = cnf xs := by
  simp only [cnf, read_snoc]
  obtain ⟨F, c⟩ := read xs
  rw [step_ne F c hx]

theorem pending_snoc_ne (xs : List Int) {x : Int} (hx : x ≠ 0) :
    pending (xs ++ [x]) = pending xs ++ [x] := by
  simp only [pending, read_snoc]
  obtain ⟨F, c⟩ := read xs
  rw [step_ne F c hx]

/-- Later integers of a stream only add clauses. -/
theorem cnf_snoc (xs : List Int) (x : Int) : ∃ G, cnf (xs ++ [x]) = cnf xs ++ G := by
  by_cases hx : x = 0
  · subst hx
    exact ⟨_, cnf_snoc_zero xs⟩
  · exact ⟨[], by rw [cnf_snoc_ne xs hx, List.append_nil]⟩

/-- Later integers of a stream only add clauses. -/
theorem cnf_append (xs ys : List Int) : ∃ G, cnf (xs ++ ys) = cnf xs ++ G := by
  induction ys generalizing xs with
  | nil => exact ⟨[], by simp⟩
  | cons y ys ih =>
    obtain ⟨G, hG⟩ := cnf_snoc xs y
    obtain ⟨G', hG'⟩ := ih (xs ++ [y])
    refine ⟨G ++ G', ?_⟩
    rw [show xs ++ y :: ys = xs ++ [y] ++ ys by simp, hG', hG, List.append_assoc]

end Dimacs

end Silmaril.Logic.SAT
