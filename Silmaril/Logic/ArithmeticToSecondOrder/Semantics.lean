module

public import Silmaril.Logic.ArithmeticToSecondOrder.Syntax
public import Silmaril.Logic.Arithmetic.Semantics
public import Silmaril.Logic.SecondOrderArithmetic.Semantics

@[expose] public section

namespace Silmaril.Logic.ArithmeticToSecondOrder

variable {n : ℕ} {𝒮 : Set (Set ℕ)}

/-- Parameter terms avoid the names reserved for binders. -/
def Safe (k h : ℕ) (e : Fin n → SecondOrderArithmetic.Term ℕ) : Prop :=
  ∀ i x, x ∈ (e i).names → x < k ∨ k + h ≤ x

theorem Safe.mono {k h h' : ℕ} {e : Fin n → SecondOrderArithmetic.Term ℕ}
    (he : Safe k h e) (hh : h' ≤ h) : Safe k h' e := by
  intro i x hx
  rcases he i x hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (by omega)

theorem Safe.fresh {k h : ℕ} {e : Fin n → SecondOrderArithmetic.Term ℕ}
    (he : Safe k (h + 1) e) (i : Fin n) : k + h ∉ (e i).names := by
  intro hx
  rcases he i (k + h) hx with h | h <;> omega

theorem Safe.extend {k h : ℕ} {e : Fin n → SecondOrderArithmetic.Term ℕ}
    (he : Safe k (h + 1) e) :
    Safe k h (Fin.cases (.var (k + h)) e) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · intro x hx
    simp only [Fin.cases_zero, SecondOrderArithmetic.Term.names, Finset.mem_singleton] at hx
    exact Or.inr (by omega)
  · exact he.mono (by omega) j

@[simp] theorem term_eval (t : Arithmetic.Term n)
    (e : Fin n → SecondOrderArithmetic.Term ℕ) (ρ : SecondOrderArithmetic.Env 𝒮 ℕ) :
    (term e t).eval ρ = t.eval (fun i => (e i).eval ρ) := by
  induction t <;> simp_all [term, Arithmetic.Term.eval, SecondOrderArithmetic.Term.eval]

/-- Adequacy is an equivalence of denotations. It does not produce an SOA proof. -/
theorem formula_eval (p : Arithmetic.Formula n) (k : ℕ)
    (e : Fin n → SecondOrderArithmetic.Term ℕ) (he : Safe k (height p) e)
    (ρ : SecondOrderArithmetic.Env 𝒮 ℕ) :
    (formula k e p).eval ρ ↔ p.eval (fun i => (e i).eval ρ) := by
  classical
  induction p generalizing ρ with
  | bot => simp [formula, falsum, SecondOrderArithmetic.Formula.eval,
      SecondOrderArithmetic.Term.eval, Arithmetic.Formula.eval]
  | equal s t => simp [formula, SecondOrderArithmetic.Formula.eval, Arithmetic.Formula.eval]
  | imp p q ip iq =>
    exact imp_congr (ip e (he.mono (Nat.le_max_left _ _)) ρ)
      (iq e (he.mono (Nat.le_max_right _ _)) ρ)
  | conj p q ip iq =>
    exact and_congr (ip e (he.mono (Nat.le_max_left _ _)) ρ)
      (iq e (he.mono (Nat.le_max_right _ _)) ρ)
  | disj p q ip iq =>
    simp only [formula, disjunction, SecondOrderArithmetic.Formula.eval,
      Arithmetic.Formula.eval, ip e (he.mono (Nat.le_max_left _ _)) ρ,
      iq e (he.mono (Nat.le_max_right _ _)) ρ]
    tauto
  | all p ip =>
    simp only [formula, SecondOrderArithmetic.Formula.eval, Arithmetic.Formula.eval]
    apply forall_congr'
    intro x
    rw [ip _ he.extend]
    have h : (fun i => ((Fin.cases (.var (k + height p)) e i :
        SecondOrderArithmetic.Term ℕ).eval (Function.update ρ (.inl (k + height p)) x))) =
        Arithmetic.extend (fun i => (e i).eval ρ) x := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [SecondOrderArithmetic.Term.eval, Arithmetic.extend]
      · exact (e j).ignores (he.fresh j) ρ x
    rw [h]
  | ex p ip =>
    simp only [formula, SecondOrderArithmetic.Formula.eval, Arithmetic.Formula.eval]
    apply exists_congr
    intro x
    rw [ip _ he.extend]
    have h : (fun i => ((Fin.cases (.var (k + height p)) e i :
        SecondOrderArithmetic.Term ℕ).eval (Function.update ρ (.inl (k + height p)) x))) =
        Arithmetic.extend (fun i => (e i).eval ρ) x := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [SecondOrderArithmetic.Term.eval, Arithmetic.extend]
      · exact (e j).ignores (he.fresh j) ρ x
    rw [h]

theorem sentence_eval (p : Arithmetic.Sentence) (ρ : SecondOrderArithmetic.Env 𝒮 ℕ) :
    (sentence p).eval ρ ↔ p.eval Fin.elim0 :=
  by
    have h := formula_eval p 0 Fin.elim0 (fun i => Fin.elim0 i) ρ
    have he : (fun i : Fin 0 => (Fin.elim0 i : SecondOrderArithmetic.Term ℕ).eval ρ) =
        Fin.elim0 := by funext i; exact Fin.elim0 i
    simpa only [sentence, he] using h

end Silmaril.Logic.ArithmeticToSecondOrder
