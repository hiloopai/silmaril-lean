module

public import Silmaril.Logic.Arithmetic.Derivation

@[expose] public section

namespace Silmaril.Logic.Arithmetic

variable {n m : ℕ} {φ : Formula n} {Γ : Context n}

/-- The six recursion and successor axioms common to Q and PA, with arbitrary
term instances. Equality and classical first-order logic belong to Derivation. -/
inductive BasicAxiom : {n : ℕ} → Formula n → Type where
  | succNonzero {n : ℕ} (t : Term n) : BasicAxiom (Formula.equal (.succ t) .zero).neg
  | succInjective {n : ℕ} (s t : Term n) :
      BasicAxiom (.imp (.equal (.succ s) (.succ t)) (.equal s t))
  | addZero {n : ℕ} (t : Term n) : BasicAxiom (.equal (.add t .zero) t)
  | addSucc {n : ℕ} (s t : Term n) : BasicAxiom (.equal (.add s (.succ t)) (.succ (.add s t)))
  | mulZero {n : ℕ} (t : Term n) : BasicAxiom (.equal (.mul t .zero) .zero)
  | mulSucc {n : ℕ} (s t : Term n) : BasicAxiom (.equal (.mul s (.succ t)) (.add (.mul s t) s))

/-- Q's essential predecessor-existence axiom. The witness is a fresh variable;
the term being considered is shifted past the existential binder. -/
def predecessor (t : Term n) : Formula n :=
  .imp (Formula.equal t .zero).neg (.ex (.equal t.shift (.succ (.var 0))))

inductive QAxiom : {n : ℕ} → Formula n → Type where
  | basic {n : ℕ} {φ : Formula n} : BasicAxiom φ → QAxiom φ
  | pred {n : ℕ} (t : Term n) : QAxiom (predecessor t)

abbrev QProof {n : ℕ} (Γ : Context n) (φ : Formula n) := Derivation QAxiom Γ φ

namespace BasicAxiom

theorem sound (h : BasicAxiom φ) : Valid φ := by
  intro e
  cases h with
  | succNonzero t => exact Nat.succ_ne_zero (t.eval e)
  | succInjective s t => exact Nat.succ.inj
  | addZero t => exact Nat.add_zero (t.eval e)
  | addSucc s t => exact Nat.add_succ (s.eval e) (t.eval e)
  | mulZero t => exact Nat.mul_zero (t.eval e)
  | mulSucc s t => exact Nat.mul_succ (s.eval e) (t.eval e)


end BasicAxiom

theorem qAxiomSound (h : QAxiom φ) : Valid φ := by
  cases h with
  | basic h => exact h.sound
  | pred t =>
    intro e h
    change t.eval e ≠ 0 at h
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
    exact ⟨k, by
      change t.shift.eval (extend e k) = Nat.succ k
      rw [Term.eval_shift]
      exact hk⟩

theorem qSound (d : QProof Γ φ) (e : Assignment n) (hΓ : Satisfies e Γ) : φ.eval e :=
  d.sound (fun h => qAxiomSound h) e hΓ

/-- A concrete closed arithmetic proof, retained as proof data. -/
def qZeroAddZero : QProof [] (.equal (.add .zero .zero) .zero : Sentence) :=
  .ax (.basic (.addZero .zero))

/-- The predecessor axiom really rules out nonstandard successor-free elements. -/
def qPredecessor (t : Term n) : QProof [] (predecessor t) := .ax (.pred t)

theorem qNotZeroEqOne : ¬ Nonempty (QProof [] (.equal .zero (.succ .zero) : Sentence)) := by
  rintro ⟨d⟩
  have h := qSound d Fin.elim0 (by simp [Satisfies])
  exact Nat.zero_ne_one h

end Silmaril.Logic.Arithmetic
