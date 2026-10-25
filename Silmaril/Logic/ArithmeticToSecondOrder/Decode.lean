module

public import Silmaril.Logic.ArithmeticToSecondOrder.Syntax

@[expose] public section

/-! A partial syntactic decoder proves that the closed arithmetic interpretation
is injective. Its disjunction tag is distinct from every other source constructor. -/

namespace Silmaril.Logic.ArithmeticToSecondOrder

open SecondOrderArithmetic

variable {n : ℕ}

def readTerm (r : ℕ → Option (Fin n)) : Term ℕ → Option (Arithmetic.Term n)
  | .var x => Arithmetic.Term.var <$> r x
  | .zero => some .zero
  | .succ t => Arithmetic.Term.succ <$> readTerm r t
  | .add s t => return .add (← readTerm r s) (← readTerm r t)
  | .mul s t => return .mul (← readTerm r s) (← readTerm r t)

def liftRead (x : ℕ) (r : ℕ → Option (Fin n)) : ℕ → Option (Fin (n + 1)) :=
  fun y => if y = x then some 0 else Fin.succ <$> r y

def readFormula {n : ℕ} (r : ℕ → Option (Fin n)) : Formula ℕ → Option (Arithmetic.Formula n)
  | .equal s t => return .equal (← readTerm r s) (← readTerm r t)
  | .imp p q => return .imp (← readFormula r p) (← readFormula r q)
  | .conj p q => return .conj (← readFormula r p) (← readFormula r q)
  | .neg (.equal .zero .zero) => some .bot
  | .neg (.conj (.neg p) (.neg q)) => return .disj (← readFormula r p) (← readFormula r q)
  | .all x p => Arithmetic.Formula.all <$> readFormula (liftRead x r) p
  | .ex x p => Arithmetic.Formula.ex <$> readFormula (liftRead x r) p
  | _ => none

@[simp] theorem readTerm_term (t : Arithmetic.Term n) (e : Fin n → ℕ)
    (r : ℕ → Option (Fin n)) (h : ∀ i, r (e i) = some i) :
    readTerm r (term (fun i => .var (e i)) t) = some t := by
  induction t <;> simp_all [term, readTerm]

theorem vars_extend (x : ℕ) (e : Fin n → ℕ) :
    (fun i => Term.var (Fin.cases x e i)) = Fin.cases (.var x) (fun i => .var (e i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem readFormula_formula (p : Arithmetic.Formula n) (k : ℕ) (e : Fin n → ℕ)
    (r : ℕ → Option (Fin n)) (hr : ∀ i, r (e i) = some i)
    (he : ∀ i, e i < k ∨ k + height p ≤ e i) :
    readFormula r (formula k (fun i => .var (e i)) p) = some p := by
  induction p with
  | bot => rfl
  | equal s t => simp [formula, readFormula, readTerm_term s e r hr, readTerm_term t e r hr]
  | imp p q ip iq | conj p q ip iq | disj p q ip iq =>
    have hp : ∀ i, e i < k ∨ k + height p ≤ e i := by
      intro i
      rcases he i with h | h
      · exact Or.inl h
      · exact Or.inr (by simp only [height] at h; omega)
    have hq : ∀ i, e i < k ∨ k + height q ≤ e i := by
      intro i
      rcases he i with h | h
      · exact Or.inl h
      · exact Or.inr (by simp only [height] at h; omega)
    simp [formula, disjunction, readFormula, ip e r hr hp, iq e r hr hq]
  | all p ip | ex p ip =>
    let x := k + height p
    have hfresh : ∀ i, e i ≠ x := by
      intro i
      rcases he i with h | h
      · omega
      · simp only [height] at h
        omega
    have hr' : ∀ i, liftRead x r (Fin.cases x e i) = some i := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [liftRead]
      · simp [liftRead, hfresh j, hr j]
    have he' : ∀ i, Fin.cases x e i < k ∨ k + height p ≤ Fin.cases x e i := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cases_zero]
        exact Or.inr (by dsimp [x]; omega)
      · simp only [Fin.cases_succ]
        rcases he j with h | h
        · exact Or.inl h
        · exact Or.inr (by simp only [height] at h; omega)
    have hi := ip (Fin.cases x e) (liftRead x r) hr' he'
    simp only [vars_extend] at hi
    simp only [formula, readFormula]
    rw [hi]
    rfl

theorem readFormula_sentence (p : Arithmetic.Sentence) :
    readFormula (fun _ => none) (sentence p) = some p := by
  have h := readFormula_formula p 0 Fin.elim0 (fun _ => none)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  have he : (fun i : Fin 0 => Term.var (Fin.elim0 i : ℕ)) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  simpa only [sentence, he] using h

theorem sentence_injective : Function.Injective sentence := by
  intro p q h
  have hh := congrArg (readFormula (n := 0) (fun _ => none)) h
  simpa only [readFormula_sentence, Option.some.injEq] using hh

end Silmaril.Logic.ArithmeticToSecondOrder
