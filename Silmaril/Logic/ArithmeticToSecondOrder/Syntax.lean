module

public import Silmaril.Logic.Arithmetic.Syntax
public import Silmaril.Logic.SecondOrderArithmetic.Base

@[expose] public section

/-! Scoped arithmetic to named second-order syntax. Binder names are chosen
from quantifier height, which substitution and renaming preserve. The name
reserve is explicit; semantic adequacy requires parameters above that reserve.
These syntax maps alone do not translate derivations. -/

namespace Silmaril.Logic.ArithmeticToSecondOrder


variable {n m : ℕ}

/-- A closed contradiction, using no number or set name. -/
def falsum : SecondOrderArithmetic.Formula ℕ := .neg (.equal .zero .zero)

/-- Disjunction expressed using the target's primitive classical connectives. -/
def disjunction (p q : SecondOrderArithmetic.Formula ℕ) : SecondOrderArithmetic.Formula ℕ := .neg (.conj (.neg p) (.neg q))

def term (e : Fin n → SecondOrderArithmetic.Term ℕ) : Arithmetic.Term n → SecondOrderArithmetic.Term ℕ
  | .var i => e i
  | .zero => .zero
  | .succ t => .succ (term e t)
  | .add s t => .add (term e s) (term e t)
  | .mul s t => .mul (term e s) (term e t)

/-- Number of nested quantifiers, independent of terms and free variables. -/
def height {n : ℕ} : Arithmetic.Formula n → ℕ
  | .bot | .equal _ _ => 0
  | .imp p q | .conj p q | .disj p q => max (height p) (height q)
  | .all p | .ex p => height p + 1

/-- Binders use names in `[k, k + height p)`. Parameters may be arbitrary
named terms; freshness conditions are needed for evaluation, not this map. -/
def formula {n : ℕ} (k : ℕ) (e : Fin n → SecondOrderArithmetic.Term ℕ) : Arithmetic.Formula n → SecondOrderArithmetic.Formula ℕ
  | .bot => falsum
  | .equal s t => .equal (term e s) (term e t)
  | .imp p q => .imp (formula k e p) (formula k e q)
  | .conj p q => .conj (formula k e p) (formula k e q)
  | .disj p q => disjunction (formula k e p) (formula k e q)
  | .all p => .all (k + height p) (formula k (Fin.cases (.var (k + height p)) e) p)
  | .ex p => .ex (k + height p) (formula k (Fin.cases (.var (k + height p)) e) p)

@[simp] theorem term_rename (t : Arithmetic.Term n) (r : Fin n → Fin m)
    (e : Fin m → SecondOrderArithmetic.Term ℕ) : term e (t.rename r) = term (e ∘ r) t := by
  induction t <;> simp_all [Arithmetic.Term.rename, term]

@[simp] theorem term_subst (t : Arithmetic.Term n) (σ : Fin n → Arithmetic.Term m)
    (e : Fin m → SecondOrderArithmetic.Term ℕ) : term e (t.subst σ) = term (fun i => term e (σ i)) t := by
  induction t <;> simp_all [Arithmetic.Term.subst, term]

@[simp] theorem height_rename (p : Arithmetic.Formula n) (r : Fin n → Fin m) :
    height (p.rename r) = height p := by
  induction p generalizing m <;> simp_all [Arithmetic.Formula.rename, height]

@[simp] theorem height_subst (p : Arithmetic.Formula n) (σ : Fin n → Arithmetic.Term m) :
    height (p.subst σ) = height p := by
  induction p generalizing m <;> simp_all [Arithmetic.Formula.subst, height]

@[simp] theorem formula_rename (p : Arithmetic.Formula n) (r : Fin n → Fin m)
    (k : ℕ) (e : Fin m → SecondOrderArithmetic.Term ℕ) :
    formula k e (p.rename r) = formula k (e ∘ r) p := by
  induction p generalizing m with
  | bot => rfl
  | equal s t => simp [Arithmetic.Formula.rename, formula]
  | imp p q ip iq | conj p q ip iq | disj p q ip iq =>
    simp [Arithmetic.Formula.rename, formula, ip, iq]
  | all p ip | ex p ip =>
    simp only [Arithmetic.Formula.rename, formula, height_rename, ip]
    congr 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Exact simultaneous substitution: the naming scheme survives substitution
without an implicit alpha-equivalence quotient. -/
@[simp] theorem formula_subst (p : Arithmetic.Formula n) (σ : Fin n → Arithmetic.Term m)
    (k : ℕ) (e : Fin m → SecondOrderArithmetic.Term ℕ) :
    formula k e (p.subst σ) = formula k (fun i => term e (σ i)) p := by
  induction p generalizing m with
  | bot => rfl
  | equal s t => simp [Arithmetic.Formula.subst, formula]
  | imp p q ip iq | conj p q ip iq | disj p q ip iq =>
    simp [Arithmetic.Formula.subst, formula, ip, iq]
  | all p ip | ex p ip =>
    simp only [Arithmetic.Formula.subst, formula, height_subst, ip]
    congr 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [Arithmetic.Term.liftSubst, Arithmetic.Term.shift, Function.comp_def]

@[simp] theorem formula_shift (p : Arithmetic.Formula n) (k x : ℕ)
    (e : Fin n → SecondOrderArithmetic.Term ℕ) :
    formula k (Fin.cases (.var x) e) p.shift = formula k e p := by
  simp [Arithmetic.Formula.shift, Function.comp_def]

@[simp] theorem formula_inst (p : Arithmetic.Formula (n + 1)) (t : Arithmetic.Term n)
    (k : ℕ) (e : Fin n → SecondOrderArithmetic.Term ℕ) :
    formula k e (p.inst t) = formula k (Fin.cases (term e t) e) p := by
  simp only [Arithmetic.Formula.inst, formula_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem formula_step (p : Arithmetic.Formula (n + 1)) (k : ℕ)
    (e : Fin n → SecondOrderArithmetic.Term ℕ) (t : SecondOrderArithmetic.Term ℕ) :
    formula k (Fin.cases t e) p.step = formula k (Fin.cases (.succ t) e) p := by
  simp only [Arithmetic.Formula.step, formula_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem formula_arithmetical (p : Arithmetic.Formula n) (k : ℕ) (e : Fin n → SecondOrderArithmetic.Term ℕ) :
    SecondOrderArithmetic.Arithmetical (formula k e p) := by
  induction p with
  | bot => exact .neg (.equal _ _)
  | equal s t => exact .equal _ _
  | imp p q ip iq => exact .imp (ip e) (iq e)
  | conj p q ip iq => exact .conj (ip e) (iq e)
  | disj p q ip iq => exact .neg (.conj (.neg (ip e)) (.neg (iq e)))
  | all p ip => exact .all _ (ip _)
  | ex p ip => exact .ex _ (ip _)

theorem term_names (t : Arithmetic.Term n) (e : Fin n → SecondOrderArithmetic.Term ℕ) :
    ∀ a ∈ (term e t).names, ∃ i, a ∈ (e i).names := by
  induction t with
  | var i => exact fun a h => ⟨i, h⟩
  | zero => simp [term, SecondOrderArithmetic.Term.names]
  | succ t it => exact it
  | add s t is it | mul s t is it =>
    intro a h
    simp only [term, SecondOrderArithmetic.Term.names, Finset.mem_union] at h
    exact h.elim (is a) (it a)

@[simp] theorem term_named_subst (t : Arithmetic.Term n)
    (e : Fin n → SecondOrderArithmetic.Term ℕ) (σ : ℕ → SecondOrderArithmetic.Term ℕ) :
    (term e t).subst σ = term (fun i => (e i).subst σ) t := by
  induction t <;> simp_all [term, SecondOrderArithmetic.Term.subst]

/-- Named substitution is capture-checked by the target syntax. Avoiding
all reserved binder names guarantees success and an exact translated result. -/
theorem formula_named_subst (p : Arithmetic.Formula n) (k x : ℕ)
    (e : Fin n → SecondOrderArithmetic.Term ℕ) (t : SecondOrderArithmetic.Term ℕ)
    (hx : x < k ∨ k + height p ≤ x)
    (ht : ∀ y ∈ t.names, y < k ∨ k + height p ≤ y) :
    (formula k e p).substNum x t =
      some (formula k (fun i => (e i).subst (fun y => if y = x then t else .var y)) p) := by
  induction p with
  | bot => rfl
  | equal s u => simp [formula, SecondOrderArithmetic.Formula.substNum]
  | imp p q ip iq | conj p q ip iq | disj p q ip iq =>
    have hxp : x < k ∨ k + height p ≤ x := by
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by simp only [height] at hx; omega)
    have hxq : x < k ∨ k + height q ≤ x := by
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by simp only [height] at hx; omega)
    have htp : ∀ y ∈ t.names, y < k ∨ k + height p ≤ y := by
      intro y hy
      rcases ht y hy with h | h
      · exact Or.inl h
      · exact Or.inr (by simp only [height] at h; omega)
    have htq : ∀ y ∈ t.names, y < k ∨ k + height q ≤ y := by
      intro y hy
      rcases ht y hy with h | h
      · exact Or.inl h
      · exact Or.inr (by simp only [height] at h; omega)
    simp [formula, disjunction, SecondOrderArithmetic.Formula.substNum,
      ip e hxp htp, iq e hxq htq]
  | all p ip | ex p ip =>
    have hne : k + height p ≠ x := by
      simp only [height] at hx
      rcases hx with hx | hx <;> omega
    have hnot : k + height p ∉ t.names := by
      intro h
      have h' := ht _ h
      simp only [height] at h'
      rcases h' with h' | h' <;> omega
    have hx' : x < k ∨ k + height p ≤ x := by
      simp only [height] at hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by omega)
    have ht' : ∀ y ∈ t.names, y < k ∨ k + height p ≤ y := by
      intro y hy
      have h := ht y hy
      simp only [height] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have he : (fun i => ((Fin.cases (.var (k + height p)) e i :
        SecondOrderArithmetic.Term ℕ).subst (fun y => if y = x then t else .var y))) =
        Fin.cases (.var (k + height p))
          (fun i => (e i).subst (fun y => if y = x then t else .var y)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [SecondOrderArithmetic.Term.subst, hne]
      · rfl
    simp [formula, SecondOrderArithmetic.Formula.substNum, hne, hnot,
      ip _ hx' ht', he]

/-- Every free name comes from a parameter term. This includes arbitrary,
possibly noninjective parameter assignments. -/
theorem formula_free (p : Arithmetic.Formula n) (k : ℕ)
    (e : Fin n → SecondOrderArithmetic.Term ℕ) :
    ∀ a ∈ (formula k e p).free, ∃ i, a ∈ (e i).names.image Sum.inl := by
  induction p with
  | bot => simp [formula, falsum, SecondOrderArithmetic.Formula.free,
      SecondOrderArithmetic.Term.names]
  | equal s t =>
    intro a ha
    simp only [formula, SecondOrderArithmetic.Formula.free, Finset.mem_image] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    simp only [Finset.mem_union] at hx
    obtain ⟨i, hi⟩ := hx.elim (term_names s e x) (term_names t e x)
    exact ⟨i, Finset.mem_image.mpr ⟨x, hi, rfl⟩⟩
  | imp p q ip iq | conj p q ip iq | disj p q ip iq =>
    intro a ha
    simp only [formula, disjunction, SecondOrderArithmetic.Formula.free,
      Finset.mem_union] at ha
    exact ha.elim (ip e a) (iq e a)
  | all p ip | ex p ip =>
    intro a ha
    simp only [formula, SecondOrderArithmetic.Formula.free, Finset.mem_erase] at ha
    obtain ⟨i, hi⟩ := ip _ a ha.2
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cases_zero, SecondOrderArithmetic.Term.names,
        Finset.image_singleton, Finset.mem_singleton]
      intro h
      exact (ha.1 h).elim
    · intro hi
      exact ⟨j, hi⟩

/-- Written names are either reserved binders or names from parameter terms. -/
theorem formula_names (p : Arithmetic.Formula n) (k : ℕ)
    (e : Fin n → SecondOrderArithmetic.Term ℕ) :
    ∀ a ∈ (formula k e p).names,
      (k ≤ a ∧ a < k + height p) ∨ ∃ i, a ∈ (e i).names := by
  induction p with
  | bot => simp [formula, falsum, SecondOrderArithmetic.Formula.names,
      SecondOrderArithmetic.Term.names]
  | equal s t =>
    intro a ha
    simp only [formula, SecondOrderArithmetic.Formula.names, Finset.mem_union] at ha
    exact Or.inr (ha.elim (term_names s e a) (term_names t e a))
  | imp p q ip iq | conj p q ip iq | disj p q ip iq =>
    intro a ha
    simp only [formula, disjunction, SecondOrderArithmetic.Formula.names,
      Finset.mem_union] at ha
    rcases ha with ha | ha
    · rcases ip e a ha with h | h
      · exact Or.inl ⟨h.1, by simp only [height]; omega⟩
      · exact Or.inr h
    · rcases iq e a ha with h | h
      · exact Or.inl ⟨h.1, by simp only [height]; omega⟩
      · exact Or.inr h
  | all p ip | ex p ip =>
    intro a ha
    simp only [formula, SecondOrderArithmetic.Formula.names, Finset.mem_insert] at ha
    rcases ha with ha | ha
    · exact Or.inl ⟨by omega, by simp only [height]; omega⟩
    · rcases ip _ a ha with h | ⟨i, hi⟩
      · exact Or.inl ⟨h.1, by simp only [height]; omega⟩
      · revert hi
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cases_zero, SecondOrderArithmetic.Term.names, Finset.mem_singleton]
          intro h
          exact Or.inl ⟨by omega, by simp only [height]; omega⟩
        · intro h
          exact Or.inr ⟨j, h⟩

/-- A closed scoped sentence becomes a closed named two-sorted sentence. -/
def sentence (p : Arithmetic.Sentence) : SecondOrderArithmetic.Formula ℕ :=
  formula 0 Fin.elim0 p

theorem sentence_closed (p : Arithmetic.Sentence) : (sentence p).Closed := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨i, _⟩ := formula_free p 0 Fin.elim0 a ha
  exact Fin.elim0 i

end Silmaril.Logic.ArithmeticToSecondOrder
