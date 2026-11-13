module

public import Silmaril.Raw.SSA.Isotope.Refinement.TypingSupport

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement
universe u v w

namespace QCtx
variable {τ : Type u} [HasQuantity τ] {n : Nat}

omit [HasQuantity τ] in
@[simp] theorem restrict_snoc_true (Γ : QCtx τ n) (A : τ) (q : Usage) (p : Fin n → Bool) :
    restrict (Γ.snoc A q) (Fin.cases true p) = (restrict Γ p).snoc A q := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- Applying the same support restriction to all three contexts preserves splitting. -/
theorem Split.restrict {Γ Γl Γr : QCtx τ n} (s : Split Γ Γl Γr) (p : Fin n → Bool) :
    Split (restrict Γ p) (restrict Γl p) (restrict Γr p) := by
  intro i
  refine ⟨(s i).1, (s i).2.1, ?_⟩
  simp only [QCtx.restrict]
  cases hp : p i
  · exact (show SlotSplit (Γ i).1 .zero .zero .zero from .left .zero)
  · exact (s i).2.2

theorem Discardable.restrict {Γ : QCtx τ n} (h : Discardable Γ) (p : Fin n → Bool) :
    Discardable (restrict Γ p) := by
  intro i
  simp only [QCtx.effective, QCtx.restrict]
  cases hp : p i
  · exact le_rfl
  · exact h i

theorem VarAllowed.restrict {Γ : QCtx τ n} {i : Fin n} (h : VarAllowed Γ i)
    (p : Fin n → Bool) (hi : p i = true) : VarAllowed (restrict Γ p) i := by
  constructor
  · simpa only [effective, QCtx.restrict, hi, Bool.true_eq, ↓reduceIte] using h.1
  · intro j hj
    simp only [QCtx.effective, QCtx.restrict]
    cases hp : p j
    · exact le_rfl
    · exact h.2 j hj

/-- Removing slots only relaxes the linearity bound of a context. -/
theorem linearity_le_restrict (Γ : QCtx τ n) (p : Fin n → Bool) :
    Γ.linearity ≤ (restrict Γ p).linearity := by
  apply le_linearity_iff.mpr
  intro i
  simp only [QCtx.restrict]
  cases hp : p i
  · exact le_top
  · exact (le_linearity_iff.mp (le_rfl : Γ.linearity ≤ Γ.linearity)) i

theorem restrict_unrestricted {Γ : QCtx τ n} (h : Γ.linearity = ⊤) (p : Fin n → Bool) :
    (restrict Γ p).linearity = ⊤ := top_le_iff.mp (h ▸ linearity_le_restrict Γ p)
end QCtx

namespace Term
variable {Φ : Type v} {n : Nat} (p : Fin n → Bool)
/-- A mask covers syntax when it retains all syntactically used variables. -/
def Covered (t : Term Φ n) : Prop := ∀ i, uses t i = true → p i = true
end Term

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ] {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

namespace HasType
/-- Transport only the quantitative context, preserving the raw term and result type. -/
def castContext {F : Fragment} {n : Nat} {Γ Δ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (h : HasType F Γ e t A) (hΓ : Γ = Δ) : HasType F Δ e t A := hΓ ▸ h

@[simp] theorem castContext_refl {F : Fragment} {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (h : HasType F Γ e t A) (he : Γ = Γ) : h.castContext he = h := rfl

/-- Strengthening away syntactically unused resources preserves the actual
native typing derivation. Bound slots keep their original default quantity. -/
def restrict {F : Fragment} {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (h : HasType F Γ e t A) (p : Fin n → Bool) (hp : Term.Covered p t) :
    HasType F (QCtx.restrict Γ p) e t A := by
  induction h with
  | var i h => exact .var i (h.restrict p (hp i (by simp [Term.uses])))
  | op hf _ ih => exact .op hf (ih p hp)
  | let₁ s _ _ iha ihb =>
    apply HasType.let₁ (s.restrict p)
    · exact iha p (fun i hi => hp i (Bool.or_eq_true_iff.mpr (.inl hi)))
    · have hb := ihb (Fin.cases true p) (fun i => Fin.cases (fun _ => rfl)
        (fun j hj => hp j (Bool.or_eq_true_iff.mpr (.inr hj))) i)
      exact hb.castContext (by simp only [QCtx.restrict_snoc_true])
  | unit h => exact .unit (h.restrict p)
  | pair s _ _ iha ihb =>
    exact .pair (s.restrict p)
      (iha p (fun i hi => hp i (Bool.or_eq_true_iff.mpr (.inl hi))))
      (ihb p (fun i hi => hp i (Bool.or_eq_true_iff.mpr (.inr hi))))
  | let₂ s _ _ iha ihb =>
    apply HasType.let₂ (s.restrict p)
    · exact iha p (fun i hi => hp i (Bool.or_eq_true_iff.mpr (.inl hi)))
    · have hb := ihb (Fin.cases true (Fin.cases true p)) (fun i => Fin.cases (fun _ => rfl)
        (fun j => Fin.cases (fun _ => rfl) (fun k hk => hp k (Bool.or_eq_true_iff.mpr (.inr hk))) j) i)
      exact hb.castContext (by simp only [QCtx.restrict_snoc_true])
  | inl f _ ih => exact .inl f (ih p hp)
  | inr f _ ih => exact .inr f (ih p hp)
  | case f s _ _ _ iha ihl ihr =>
    apply HasType.case f (s.restrict p)
    · exact iha p (fun i hi => hp i (Bool.or_eq_true_iff.mpr (.inl hi)))
    · have hl := ihl (Fin.cases true p) (fun i => Fin.cases (fun _ => rfl)
        (fun j hj => hp j (Bool.or_eq_true_iff.mpr (.inr (Bool.or_eq_true_iff.mpr (.inl hj))))) i)
      exact hl.castContext (QCtx.restrict_snoc_true _ _ _ _)
    · have hr := ihr (Fin.cases true p) (fun i => Fin.cases (fun _ => rfl)
        (fun j hj => hp j (Bool.or_eq_true_iff.mpr (.inr (Bool.or_eq_true_iff.mpr (.inr hj))))) i)
      exact hr.castContext (QCtx.restrict_snoc_true _ _ _ _)
  | abort f _ ih => exact .abort f (ih p hp)
  | iter f s hu hi _ _ iha ihb =>
    apply HasType.iter f (s.restrict p) (QCtx.restrict_unrestricted hu p) hi
    · exact iha p (fun i hi => hp i (Bool.or_eq_true_iff.mpr (.inl hi)))
    · have hb := ihb (Fin.cases true p) (fun i => Fin.cases (fun _ => rfl)
        (fun j hj => hp j (Bool.or_eq_true_iff.mpr (.inr hj))) i)
      exact hb.castContext (by simp only [QCtx.restrict_snoc_true])

/-- Any mask covering the term is a native quantitative weakening. -/
theorem coveringWeakening {F : Fragment} {n : Nat} {Γ : QCtx τ n} {e : ε}
    {t : Term Φ n} {A : τ} (h : HasType F Γ e t A)
    (p : Fin n → Bool) (hp : Term.Covered p t) :
    QCtx.Weakening Γ (QCtx.restrict Γ p) id := by
  apply QCtx.weakening_restrict
  intro i hi
  apply h.unused_discardable
  cases ht : Term.uses t i
  · rfl
  · exact False.elim (Bool.noConfusion ((hp i ht).symm.trans hi))

/-- Canonical restriction to precisely the syntactic support. -/
def support {F : Fragment} {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (h : HasType F Γ e t A) : HasType F (QCtx.restrict Γ (Term.uses t)) e t A :=
  h.restrict (Term.uses t) (fun _ => id)

end HasType
end Silmaril.Isotope.Refinement
