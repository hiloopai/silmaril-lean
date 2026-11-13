module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Effects
public import Silmaril.Raw.SSA.Isotope.Refinement.SubstitutionStructural

/-! # Categorical interpretation of native quantitative substitutions -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation

universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε) {F : Fragment} (K : ControlData M F)

/-- Execute retained substitution entries in their packed order. A zero slot
contributes no computation and requires no typing of its arbitrary syntax. -/
def denoteSubstitution {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε}
    {σ : Fin n → Term Φ m} (h : Substitution F Γ e σ Δ) : M.Hom (packed Γ) (packed Δ) := by
  induction h with
  | nil hd => exact discard M hd
  | zero _ _ _ ih => exact ih
  | cons s _ ha _ _ _ _ ih => exact M.compose (split M s) (M.tensor ih (denote M K ha))

@[simp] theorem denoteSubstitution_nil {m : Nat} {Γ : QCtx τ m} {e : ε}
    (hd : Γ.Discardable) :
    denoteSubstitution M K (Substitution.nil (F := F) (e := e) hd) = discard M hd := rfl

@[simp] theorem denoteSubstitution_zero {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n}
    {e : ε} {σ : Fin n → Term Φ m} (h : Substitution F Γ e σ Δ) (a : Term Φ m) (A : τ) :
    denoteSubstitution M K (.zero h a A) = denoteSubstitution M K h := rfl

@[simp] theorem denoteSubstitution_cons {n m : Nat} {Γ Γl Γr : QCtx τ m} {Δ : QCtx τ n}
    {e el er : ε} {σ : Fin n → Term Φ m} {a : Term Φ m} {A : τ} {q : Quantity}
    (s : Γ.Split Γl Γr) (h : Substitution F Γl el σ Δ) (ha : HasType F Γr er a A)
    (hq : q ≤ Γr.linearity) (hc : EffectSystem.commutes el er) (hl : el ≤ e) (hr : er ≤ e) :
    denoteSubstitution M K (.cons s h ha hq hc hl hr) =
      M.compose (split M s) (M.tensor (denoteSubstitution M K h) (denote M K ha)) := rfl

/-- The aggregate native effect bound also bounds execution of the packed substitution. -/
theorem denoteSubstitution_effect (E : ControlEffects K) {n m : Nat}
    {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε} {σ : Fin n → Term Φ m}
    (h : Substitution F Γ e σ Δ) : M.hasEffect e (denoteSubstitution M K h) := by
  induction h with
  | nil hd => exact M.effect_mono bot_le (discard_pure M hd)
  | zero _ _ _ ih => exact ih
  | cons s _ ha _ _ hl hr ih =>
    exact M.compose_effect (M.effect_mono bot_le (split_pure M s))
      (M.tensor_effect (M.effect_mono hl ih) (M.effect_mono hr (denote_effect K E ha)))

/-- Widening only the aggregate effect leaves the interpreted substitution unchanged. -/
theorem denoteSubstitution_effectMono {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n}
    {e e' : ε} {σ : Fin n → Term Φ m} (h : Substitution F Γ e σ Δ) (he : e ≤ e') :
    denoteSubstitution M K (h.effectMono he) = denoteSubstitution M K h := by
  induction h with
  | nil => rfl
  | zero _ _ _ ih => exact ih he
  | cons => rfl

end Silmaril.Isotope.Refinement.Models.Denotation

namespace Silmaril.Isotope.Refinement.Substitution

universe u v w
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ] {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment}

/-- The side conditions needed to substitute through a body of effect `η`.
Every retained entry satisfies its own quantitative effect allowance and mover
condition; a zero entry remains completely unrestricted syntax. -/
def EffectAllowed (p : Polarity) (η : ε) {n m : Nat} {Γ : QCtx τ m} {Δ : QCtx τ n}
    {e : ε} {σ : Fin n → Term Φ m} (h : Substitution F Γ e σ Δ) : Prop := by
  induction h with
  | nil => exact True
  | zero _ _ _ ih => exact ih
  | @cons m n Γ Γl Γr Δ e el er σ a A q s h ha hq hc hl hr ih =>
    exact ih ∧ q ≤ EffectSystem.quantity p er ∧ EffectSystem.moves p er η

theorem EffectAllowed.effectMono {p : Polarity} {η : ε} {n m : Nat}
    {Γ : QCtx τ m} {Δ : QCtx τ n} {e e' : ε} {σ : Fin n → Term Φ m}
    {h : Substitution F Γ e σ Δ} (hh : EffectAllowed p η h) (he : e ≤ e') :
    EffectAllowed p η (h.effectMono he) := by
  induction h with
  | nil => trivial
  | zero _ _ _ ih => exact ih hh he
  | cons => exact hh

theorem EffectAllowed.bodyEffectMono {p : Polarity} {η η' : ε} {n m : Nat}
    {Γ : QCtx τ m} {Δ : QCtx τ n} {e : ε} {σ : Fin n → Term Φ m}
    {h : Substitution F Γ e σ Δ} (hh : EffectAllowed p η h) (he : η' ≤ η) :
    EffectAllowed p η' h := by
  induction h with
  | nil => trivial
  | zero _ _ _ ih => exact ih hh
  | cons _ _ _ _ _ _ _ ih =>
    exact ⟨ih hh.1, hh.2.1, EffectSystem.moves_antitone p le_rfl he hh.2.2⟩

end Silmaril.Isotope.Refinement.Substitution
