module

public import Silmaril.Logic.SetTheory.Inductive.Syntax
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! # Tarski semantics and the substitution lemma for scoped membership syntax -/

namespace Silmaril.Logic.SetTheory.Inductive

universe u

namespace Formula

/-- Tarski satisfaction in an arbitrary membership structure. -/
def eval {M : Type u} [Membership M M] {n : Nat} (E : Fin n → M) : Formula n → Prop
  | .bot => False
  | .eq x y => E x = E y
  | .mem x y => E x ∈ E y
  | .neg p => ¬ p.eval E
  | .imp p q => p.eval E → q.eval E
  | .iff p q => p.eval E ↔ q.eval E
  | .conj p q => p.eval E ∧ q.eval E
  | .disj p q => p.eval E ∨ q.eval E
  | .all p => ∀ a : M, p.eval (Fin.cons a E)
  | .ex p => ∃ a : M, p.eval (Fin.cons a E)

/-- A sentence is evaluated in the unique empty assignment. -/
def holds {M : Type u} [Membership M M] (p : Sentence) : Prop :=
  p.eval (Fin.elim0 : Fin 0 → M)

@[simp] theorem cons_comp_lift {M : Type u} {n m : Nat} (E : Fin m → M)
    (a : M) (σ : Fin n → Fin m) : Fin.cons a E ∘ lift σ = Fin.cons a (E ∘ σ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Capture-avoiding syntactic substitution agrees with composition of assignments. -/
@[simp] theorem eval_subst {M : Type u} [Membership M M] {n m : Nat}
    (p : Formula n) (σ : Fin n → Fin m) (E : Fin m → M) :
    (p.subst σ).eval E ↔ p.eval (E ∘ σ) := by
  induction p generalizing m <;> simp [subst, eval, *, cons_comp_lift]

@[simp] theorem eval_weaken {M : Type u} [Membership M M] {n : Nat}
    (p : Formula n) (E : Fin n → M) (a : M) : p.weaken.eval (Fin.cons a E) ↔ p.eval E := by
  simp [weaken, Function.comp_def]

@[simp] theorem eval_instantiate {M : Type u} [Membership M M] {n : Nat}
    (p : Formula (n + 1)) (t : Term n) (E : Fin n → M) :
    (p.instantiate t).eval E ↔ p.eval (Fin.cons (E t) E) := by
  rw [instantiate, eval_subst]
  have h : E ∘ Fin.cases t id = Fin.cons (E t) E := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [h]

end Formula
end Silmaril.Logic.SetTheory.Inductive
