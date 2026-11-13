module

public import Silmaril.Proofs.Logic.SAT.LRAT.Basic

@[expose] public section

/-!
# A reference LRAT checker: RAT steps and soundness of the run

* `CNF.sat_cons_of_rat`: the semantic RAT lemma. If every clause `D` of `G` containing `-p`
  gives `G.Implies (C ++ (D without -p))` and `p ∈ C`, then every model `τ` of `G` yields a
  model of `C :: G` (`τ` itself if it satisfies `C`, else `τ` with `p` made true,
  `Assignment.flip`). RAT additions need not be implied, but they preserve satisfiability.
* `ratOk_sat`: a valid RAT step keeps the database satisfiable; `Step.sat_apply`: every valid
  step does (`F.Sat → (clauses db).Sat` is the forward invariant along a run, `sat_init`).
* `run_unsat`: a successful run makes its starting database unsatisfiable (the invariant read
  backwards from the empty clause); `run_sound` (from `Implied F db`) and **`check_sound`**.

The converse invariant, `(clauses db).Sat → F.Sat`, can fail after deletions. A RAT addition
alone preserves satisfiability in both directions: every model of `C :: G` is a model of `G`.
Initially `clauses (init 1 F) = F` (`clauses_init`), so both directions hold.
-/

namespace Silmaril.Logic.SAT

/-- `τ` with the variable of `p` set so that `p` is true. -/
def Assignment.flip (τ : Assignment) (p : Lit) : Assignment :=
  fun v => if v = p.var then p.pos else τ v

theorem Lit.eval_flip_self (τ : Assignment) (p : Lit) : p.eval (τ.flip p) = true := by
  simp [Lit.eval, Assignment.flip]

theorem Lit.eval_flip_of_var_ne (τ : Assignment) {p l : Lit} (h : l.var ≠ p.var) :
    l.eval (τ.flip p) = l.eval τ := by
  simp [Lit.eval, Assignment.flip, h]

/-- A true literal other than `-p` stays true when `p` is made true. -/
theorem Lit.eval_flip_of_true {τ : Assignment} {p l : Lit} (hl : l.eval τ = true)
    (hne : l ≠ -p) : l.eval (τ.flip p) = true := by
  by_cases hv : l.var = p.var
  · rcases Int.natAbs_eq_natAbs_iff.1 hv with rfl | rfl
    · exact Lit.eval_flip_self τ l
    · exact absurd rfl hne
  · rw [Lit.eval_flip_of_var_ne τ hv, hl]

/-- **The RAT lemma**: a clause `C` containing `p` such that every clause `D` of `G` with
`-p ∈ D` gives `G.Implies (C ++ (D without -p))` keeps `G` satisfiable. -/
theorem CNF.sat_cons_of_rat {G : CNF} {C : Clause} {p : Lit} (hp : p ∈ C)
    (hrat : ∀ D ∈ G, -p ∈ D → G.Implies (C ++ D.filter (· != -p))) {τ : Assignment}
    (hτ : G.eval τ = true) : ∃ τ' : Assignment, CNF.eval τ' (C :: G) = true := by
  by_cases hC : C.eval τ = true
  · exact ⟨τ, by simp [CNF.eval, List.all_cons] at hτ ⊢; exact ⟨hC, hτ⟩⟩
  have hCf : ∀ l ∈ C, l.eval τ = false :=
    (Clause.eval_eq_false_iff τ C).1 (by simpa using hC)
  refine ⟨τ.flip p, (CNF.eval_eq_true_iff _ _).2 fun D hD => ?_⟩
  rcases List.mem_cons.1 hD with rfl | hD
  · exact (Clause.eval_eq_true_iff _ _).2 ⟨p, hp, Lit.eval_flip_self τ p⟩
  have hl : ∃ l ∈ D, l ≠ -p ∧ l.eval τ = true := by
    by_cases hn : -p ∈ D
    · obtain ⟨l, hl, hlt⟩ := (Clause.eval_eq_true_iff _ _).1 (hrat D hD hn τ hτ)
      rcases List.mem_append.1 hl with hl | hl
      · rw [hCf l hl] at hlt; cases hlt
      · obtain ⟨hlD, hlp⟩ := List.mem_filter.1 hl
        exact ⟨l, hlD, by simpa using hlp, hlt⟩
    · obtain ⟨l, hlD, hlt⟩ := (Clause.eval_eq_true_iff _ _).1
        ((CNF.eval_eq_true_iff τ G).1 hτ D hD)
      exact ⟨l, hlD, fun h => hn (h ▸ hlD), hlt⟩
  obtain ⟨l, hlD, hne, hlt⟩ := hl
  exact (Clause.eval_eq_true_iff _ _).2 ⟨l, hlD, Lit.eval_flip_of_true hlt hne⟩

end Silmaril.Logic.SAT

namespace Silmaril.Logic.SAT.LRAT

theorem clauses_cons (id : Nat) (C : Clause) (db : DB) : clauses ((id, C) :: db) = C :: clauses db :=
  rfl

theorem clauses_init (n : Nat) (F : CNF) : clauses (init n F) = F := by
  induction F generalizing n with
  | nil => rfl
  | cons C F ih => exact congrArg (C :: ·) (ih (n + 1))

/-- Every clause of a database is implied by its clauses. -/
theorem implied_clauses (db : DB) : Implied (clauses db) db :=
  fun _ hp => CNF.Implies.of_mem (List.mem_map_of_mem hp)

/-- A valid RUP addition is implied by the database. -/
theorem addOk_implies_db {db : DB} {lits : Clause} {hints : List Nat}
    (h : addOk db lits hints = true) : (clauses db).Implies lits :=
  addOk_implies (implied_clauses db) h

/-- The models of a database are models of a database with fewer entries. -/
theorem eval_clauses_sub {db db' : DB} (hsub : ∀ e ∈ db', e ∈ db) {τ : Assignment}
    (h : (clauses db).eval τ = true) : (clauses db').eval τ = true :=
  (CNF.eval_eq_true_iff _ _).2 fun _ hC => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hC
    exact (CNF.eval_eq_true_iff _ _).1 h _ (List.mem_map_of_mem (hsub e he))

/-- **A valid RAT addition keeps the database satisfiable.** -/
theorem ratOk_sat {db : DB} {lits : Clause} {groups : List (Nat × List Nat)}
    (h : ratOk db lits groups = true) (id : Nat) {τ : Assignment}
    (hτ : (clauses db).eval τ = true) : ∃ τ', (clauses ((id, lits) :: db)).eval τ' = true := by
  match lits, h with
  | p :: rest, h =>
    have hall := (Bool.and_eq_true _ _ ▸ h).2
    refine CNF.sat_cons_of_rat List.mem_cons_self (fun D hD hn => ?_) hτ
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hD
    have he' := List.all_eq_true.1 hall e he
    have hc : e.2.contains (-p) = true := List.elem_iff.2 hn
    rw [hc, Bool.not_true, Bool.false_or, List.any_eq_true] at he'
    obtain ⟨g, -, hg⟩ := he'
    have hok := (Bool.and_eq_true _ _ ▸ hg).2
    exact addOk_implies_db hok

/-- **Every valid step keeps the database satisfiable**: the forward invariant
`F.Sat → (clauses db).Sat` of a run, from `sat_init`. -/
theorem Step.sat_apply {db : DB} {s : Step} (h : s.ok db = true) {τ : Assignment}
    (hτ : (clauses db).eval τ = true) : ∃ τ', (clauses (s.apply db)).eval τ' = true := by
  cases s with
  | add id lits hints =>
    refine ⟨τ, ?_⟩
    simp only [Step.apply, clauses_cons, CNF.eval, List.all_cons, Bool.and_eq_true]
    exact ⟨addOk_implies_db h τ hτ, hτ⟩
  | del ids => exact ⟨τ, eval_clauses_sub (db' := delete db ids) (fun _ he => (List.mem_filter.1 he).1) hτ⟩
  | rat id lits groups => exact ratOk_sat h id hτ

/-- The invariant holds initially, with equality. -/
theorem sat_init (F : CNF) : F.Sat ↔ (clauses (init 1 F)).Sat := by rw [clauses_init]

theorem CNF.unsat_of_forall {F : CNF} (h : ∀ τ, F.eval τ = true → False) : F.Unsat := by
  intro τ
  cases hτ : F.eval τ with
  | false => rfl
  | true => exact (h τ hτ).elim

/-- A database whose every model gives a model of a refuted one is refuted. -/
theorem unsat_of_sat_step {db db' : DB}
    (hstep : ∀ τ, (clauses db).eval τ = true → ∃ τ', (clauses db').eval τ' = true)
    (h' : (clauses db').Unsat) : (clauses db).Unsat :=
  CNF.unsat_of_forall fun τ hτ => by
    obtain ⟨τ', hτ'⟩ := hstep τ hτ
    have hf : (clauses db').eval τ' = false := h' τ'
    rw [hτ'] at hf
    cases hf

/-- **A successful run refutes its starting database.** -/
theorem run_unsat {ps : List Step} : ∀ {db : DB}, run db ps = true → (clauses db).Unsat := by
  induction ps with
  | nil => intro db h; cases h
  | cons p ps ih =>
    intro db h
    cases p with
    | del ids => exact unsat_of_sat_step (fun τ hτ => Step.sat_apply (s := .del ids) rfl hτ) (ih h)
    | add id lits hints =>
      have hok : addOk db lits hints = true := (Bool.and_eq_true _ _ ▸ h).1
      cases lits with
      | nil => exact CNF.Unsat.of_implies_nil (addOk_implies_db hok)
      | cons l lits =>
        have hrest : run ((id, l :: lits) :: db) ps = true := (Bool.and_eq_true _ _ ▸ h).2
        exact unsat_of_sat_step (fun τ hτ => Step.sat_apply (s := .add id (l :: lits) hints) hok hτ)
          (ih hrest)
    | rat id lits groups =>
      have hok : ratOk db lits groups = true := (Bool.and_eq_true _ _ ▸ h).1
      have hrest : run ((id, lits) :: db) ps = true := (Bool.and_eq_true _ _ ▸ h).2
      exact unsat_of_sat_step (fun τ hτ => ratOk_sat hok id hτ) (ih hrest)

/-- Running a proof on a database implied by `F` succeeds only if `F` implies the empty
clause. -/
theorem run_sound {F : CNF} {ps : List Step} {db : DB} (hdb : Implied F db)
    (h : run db ps = true) : F.Implies [] := by
  intro τ hF
  have hτ : (clauses db).eval τ = true := (CNF.eval_eq_true_iff _ _).2 fun _ hC => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hC
    exact hdb e he τ hF
  rw [run_unsat h τ] at hτ
  cases hτ

/-- **Soundness of the LRAT checker** (RUP and RAT): an accepted proof refutes `F`. -/
theorem check_sound {F : CNF} {proof : List Step} (h : check F proof = true) : F.Unsat := by
  have := run_unsat (db := init 1 F) h
  rwa [clauses_init] at this

end Silmaril.Logic.SAT.LRAT
