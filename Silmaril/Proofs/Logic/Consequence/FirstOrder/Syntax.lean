module

public import Silmaril.Logic.Consequence.FirstOrder.Syntax.Defs

/-!
# Proofs for unsorted first-order renaming and substitution
-/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.FirstOrder.Syntax

open Silmaril.Logic.Institution.Examples.UFOL

variable {Sg : Signature} (M : Structure Sg)

theorem eval_rename {k m : ℕ} (ρ : Fin k → Fin m) (η : Fin m → M.carrier) :
    ∀ t : Term Sg k, (t.rename ρ).eval M η = t.eval M (η ∘ ρ)
  | .var i => rfl
  | .app o args => by
    simp only [Term.rename, Term.eval]
    exact congrArg (M.op o) (funext fun j => eval_rename ρ η (args j))

theorem eval_subst {k m : ℕ} (σ : Fin k → Term Sg m) (η : Fin m → M.carrier) :
    ∀ t : Term Sg k, (t.subst σ).eval M η = t.eval M fun i => (σ i).eval M η
  | .var i => rfl
  | .app o args => by
    simp only [Term.subst, Term.eval]
    exact congrArg (M.op o) (funext fun j => eval_subst σ η (args j))

theorem cons_liftRename {k m : ℕ} (ρ : Fin k → Fin m) (η : Fin m → M.carrier) (x : M.carrier) :
    (Fin.cons x η : Fin (m + 1) → M.carrier) ∘ liftRename ρ = Fin.cons x (η ∘ ρ) := by
  funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [liftRename]

theorem cons_liftSubst {k m : ℕ} (σ : Fin k → Term Sg m) (η : Fin m → M.carrier) (x : M.carrier) :
    (fun i => (liftSubst σ i).eval M (Fin.cons x η : Fin (m + 1) → M.carrier)) =
      Fin.cons x fun i => (σ i).eval M η := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · simp only [liftSubst, Fin.cases_succ, Fin.cons_succ, Term.shift, eval_rename]
    rfl

theorem holds_rename : ∀ {k m : ℕ} (ρ : Fin k → Fin m) (φ : Formula Sg k) (η : Fin m → M.carrier),
    (φ.rename ρ).Holds M η ↔ φ.Holds M (η ∘ ρ)
  | _, _, ρ, .eq t u, η => by simp [Formula.rename, Formula.Holds, eval_rename]
  | _, _, ρ, .rel r args, η => by
    simp only [Formula.rename, Formula.Holds, eval_rename]
  | _, _, _, .tt, _ => Iff.rfl
  | _, _, ρ, .not φ, η => not_congr (holds_rename ρ φ η)
  | _, _, ρ, .and φ ψ, η => and_congr (holds_rename ρ φ η) (holds_rename ρ ψ η)
  | _, _, ρ, .all φ, η => by
    simp only [Formula.rename, Formula.Holds]
    exact forall_congr' fun x => by rw [holds_rename, cons_liftRename]

theorem holds_subst : ∀ {k m : ℕ} (σ : Fin k → Term Sg m) (φ : Formula Sg k)
    (η : Fin m → M.carrier), (φ.subst σ).Holds M η ↔ φ.Holds M fun i => (σ i).eval M η
  | _, _, σ, .eq t u, η => by simp [Formula.subst, Formula.Holds, eval_subst]
  | _, _, σ, .rel r args, η => by
    simp only [Formula.subst, Formula.Holds, eval_subst]
  | _, _, _, .tt, _ => Iff.rfl
  | _, _, σ, .not φ, η => not_congr (holds_subst σ φ η)
  | _, _, σ, .and φ ψ, η => and_congr (holds_subst σ φ η) (holds_subst σ ψ η)
  | _, _, σ, .all φ, η => by
    simp only [Formula.subst, Formula.Holds]
    exact forall_congr' fun x => by rw [holds_subst, cons_liftSubst]

theorem holds_shift {k : ℕ} (φ : Formula Sg k) (η : Fin k → M.carrier) (x : M.carrier) :
    φ.shift.Holds M (Fin.cons x η) ↔ φ.Holds M η := by
  rw [Formula.shift, holds_rename]; rfl

theorem holds_inst {k : ℕ} (φ : Formula Sg (k + 1)) (t : Term Sg k) (η : Fin k → M.carrier) :
    (φ.inst t).Holds M η ↔ φ.Holds M (Fin.cons (t.eval M η) η) := by
  rw [Formula.inst, holds_subst]
  apply iff_of_eq; congr 1; funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

/-! ## Signature morphisms commute with renaming and substitution -/

section Map

variable {Sg' : Signature} (σ : Sg ⟶ Sg')

theorem term_map_rename {k m : ℕ} (ρ : Fin k → Fin m) :
    ∀ t : Term Sg k, (t.rename ρ).map σ = (t.map σ).rename ρ
  | .var _ => rfl
  | .app o args => by
    simp only [Term.rename, Term.map]
    exact congrArg (Term.app _) (funext fun j => term_map_rename ρ (args j))

theorem term_map_subst {k m : ℕ} (τ : Fin k → Term Sg m) :
    ∀ t : Term Sg k, (t.subst τ).map σ = (t.map σ).subst fun i => (τ i).map σ
  | .var _ => rfl
  | .app o args => by
    simp only [Term.subst, Term.map]
    exact congrArg (Term.app _) (funext fun j => term_map_subst τ (args j))

theorem map_liftSubst {k m : ℕ} (τ : Fin k → Term Sg m) (i : Fin (k + 1)) :
    (liftSubst τ i).map σ = liftSubst (fun i => (τ i).map σ) i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · simp only [liftSubst, Fin.cases_succ, Term.shift, term_map_rename]

theorem formula_map_rename : ∀ {k m : ℕ} (ρ : Fin k → Fin m) (φ : Formula Sg k),
    (φ.rename ρ).map σ = (φ.map σ).rename ρ
  | _, _, ρ, .eq t u => by simp [Formula.rename, Formula.map, term_map_rename]
  | _, _, ρ, .rel r args => by
    simp only [Formula.rename, Formula.map]
    exact congrArg (Formula.rel _) (funext fun j => term_map_rename σ ρ (args j))
  | _, _, _, .tt => rfl
  | _, _, ρ, .not φ => by simp [Formula.rename, Formula.map, formula_map_rename ρ φ]
  | _, _, ρ, .and φ ψ => by
    simp [Formula.rename, Formula.map, formula_map_rename ρ φ, formula_map_rename ρ ψ]
  | _, _, ρ, .all φ => by simp [Formula.rename, Formula.map, formula_map_rename (liftRename ρ) φ]

theorem formula_map_subst : ∀ {k m : ℕ} (τ : Fin k → Term Sg m) (φ : Formula Sg k),
    (φ.subst τ).map σ = (φ.map σ).subst fun i => (τ i).map σ
  | _, _, τ, .eq t u => by simp [Formula.subst, Formula.map, term_map_subst]
  | _, _, τ, .rel r args => by
    simp only [Formula.subst, Formula.map]
    exact congrArg (Formula.rel _) (funext fun j => term_map_subst σ τ (args j))
  | _, _, _, .tt => rfl
  | _, _, τ, .not φ => by simp [Formula.subst, Formula.map, formula_map_subst τ φ]
  | _, _, τ, .and φ ψ => by
    simp [Formula.subst, Formula.map, formula_map_subst τ φ, formula_map_subst τ ψ]
  | _, _, τ, .all φ => by
    simp only [Formula.subst, Formula.map, formula_map_subst (liftSubst τ) φ]
    exact congrArg Formula.all (congrArg (Formula.subst · (φ.map σ)) (funext (map_liftSubst σ τ)))

theorem formula_map_inst {k : ℕ} (φ : Formula Sg (k + 1)) (t : Term Sg k) :
    (φ.inst t).map σ = (φ.map σ).inst (t.map σ) := by
  rw [Formula.inst, formula_map_subst]
  congr 1; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl

theorem formula_map_shift {k : ℕ} (φ : Formula Sg k) : φ.shift.map σ = (φ.map σ).shift :=
  formula_map_rename σ Fin.succ φ

end Map

end Silmaril.Proofs.Logic.Consequence.FirstOrder.Syntax
