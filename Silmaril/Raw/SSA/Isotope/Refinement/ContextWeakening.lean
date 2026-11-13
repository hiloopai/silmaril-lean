module

public import Silmaril.Raw.SSA.Isotope.Refinement.Contexts

@[expose] public section

/-! # The context premises coincide with the written weakening rules -/

namespace Silmaril.Isotope.Refinement.QCtx

universe u
variable {τ : Type u} [HasQuantity τ] {n m : Nat}

omit [HasQuantity τ] in
theorem snoc_tail (Γ : QCtx τ (n + 1)) :
    snoc (fun i => Γ i.succ) (Γ 0).1 (Γ 0).2 = Γ := by
  funext i
  exact Fin.cases (Prod.eta _) (fun _ => rfl) i

namespace Weakening

/-- Retained variables have exactly the same type. -/
theorem types {Γ : QCtx τ n} {Δ : QCtx τ m} {ρ : Fin m → Fin n}
    (h : Weakening Γ Δ ρ) : ∀ i, (Γ (ρ i)).1 = (Δ i).1 := by
  induction h with
  | nil => intro i; exact Fin.elim0 i
  | cons _ _ ih => intro i; exact Fin.cases rfl ih i
  | skip _ _ ih => exact ih

/-- The finite-index context map is an embedding, never a contraction. -/
theorem injective {Γ : QCtx τ n} {Δ : QCtx τ m} {ρ : Fin m → Fin n}
    (h : Weakening Γ Δ ρ) : Function.Injective ρ := by
  induction h with
  | nil => intro i; exact Fin.elim0 i
  | cons _ _ ih =>
    intro i j h
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j => exact (Fin.succ_ne_zero _ h.symm).elim
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (Fin.succ_ne_zero _ h).elim
      | succ j => exact congrArg Fin.succ (ih (Fin.succ_injective _ h))
  | skip _ _ ih => exact fun _ _ h => ih (Fin.succ_injective _ h)

/-- The source permits every effective use allowed by the destination. -/
theorem effective_le {Γ : QCtx τ n} {Δ : QCtx τ m} {ρ : Fin m → Fin n}
    (h : Weakening Γ Δ ρ) : ∀ i, effective Δ i ≤ effective Γ (ρ i) := by
  induction h with
  | nil => intro i; exact Fin.elim0 i
  | cons _ hq ih => intro i; exact Fin.cases hq ih i
  | skip _ _ ih => exact ih

/-- Every omitted source variable really is discardable. -/
theorem omitted {Γ : QCtx τ n} {Δ : QCtx τ m} {ρ : Fin m → Fin n}
    (h : Weakening Γ Δ ρ) : ∀ j, (∀ i, ρ i ≠ j) → Usage.zero ≤ effective Γ j := by
  induction h with
  | nil => intro j; exact Fin.elim0 j
  | cons _ _ ih =>
    intro j hj
    cases j using Fin.cases with
    | zero => exact (hj 0 rfl).elim
    | succ j => exact ih j (fun i hi => hj i.succ (congrArg Fin.succ hi))
  | skip _ hq ih =>
    intro j hj
    cases j using Fin.cases with
    | zero => exact hq
    | succ j => exact ih j (fun i hi => hj i (congrArg Fin.succ hi))

end Weakening

/-- The pointwise discardability premise is exactly weakening to the empty context. -/
theorem discardable_iff_weakening_nil {Γ : QCtx τ n} :
    Discardable Γ ↔ Weakening Γ nil Fin.elim0 := by
  constructor
  · intro h
    induction n with
    | zero =>
      have he : Γ = nil := funext (fun i => Fin.elim0 i)
      subst Γ
      exact .nil
    | succ n ih =>
      have tail : Discardable (fun i : Fin n => Γ i.succ) := fun i => h i.succ
      have hw := Weakening.skip (ih tail) (h 0)
      have he := snoc_tail Γ
      rw [he] at hw
      convert hw using 1
  · intro h i
    exact h.omitted i (fun j => Fin.elim0 j)

/-- The variable premise is exactly weakening to that variable used once. -/
theorem varAllowed_iff_weakening_singleton {Γ : QCtx τ n} (i : Fin n) :
    VarAllowed Γ i ↔
      Weakening Γ (nil.snoc (Γ i).1 (.used .linear)) (fun _ => i) := by
  constructor
  · intro h
    induction n with
    | zero => exact Fin.elim0 i
    | succ n ih =>
      cases i using Fin.cases with
      | zero =>
        have tail : Discardable (fun j : Fin n => Γ j.succ) :=
          fun j => h.2 j.succ (Fin.succ_ne_zero _)
        have hw := Weakening.cons (discardable_iff_weakening_nil.mp tail) h.1
        have he := snoc_tail Γ
        rw [he] at hw
        convert hw using 1
        funext j
        exact Fin.cases rfl (fun k => Fin.elim0 k) j
      | succ i =>
        have tail : VarAllowed (fun j : Fin n => Γ j.succ) i := by
          refine ⟨h.1, ?_⟩
          intro j hji
          exact h.2 j.succ (fun he => hji (Fin.succ_injective _ he))
        have hw := Weakening.skip (ih i tail) (h.2 0 (Ne.symm (Fin.succ_ne_zero _)))
        have he := snoc_tail Γ
        rw [he] at hw
        exact hw
  · intro h
    refine ⟨h.effective_le 0, ?_⟩
    intro j hj
    exact h.omitted j (fun _ => Ne.symm hj)

end Silmaril.Isotope.Refinement.QCtx
