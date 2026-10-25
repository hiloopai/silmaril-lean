module

public import Silmaril.Logic.HOLLight.Kernel.Structural
public import Silmaril.Logic.HOLLight.Semantics.Logic
public import Silmaril.Logic.HOLLight.Semantics.Substitution
public import Silmaril.Logic.HOLLight.Semantics.TypeSubstitution

@[expose] public section

/-!
# Semantic validity and entailment

Type variables range over nonempty carriers in `Type u`; free term variables
range independently over the denotation of their annotated type. User axioms
are assumptions on a model and are never silently asserted in the metatheory.
-/

namespace Silmaril.Logic.HOLLight

universe u

def Holds {sig : Signature} (M : Model.{u} sig) (ρ : TypeValuation.{u})
    (ν : FreeEnv M ρ) (p : Tm) : Prop :=
  ∃ value, Eval M ρ ν BoundEnv.empty p .bool value ∧ Carrier.Truth value

def Valid {sig : Signature} (M : Model.{u} sig) (p : Tm) : Prop :=
  ∀ ρ ν, Holds M ρ ν p

def Models {sig : Signature} (M : Model.{u} sig) (theory : Theory) : Prop :=
  ∀ p ∈ theory, Valid M p

def HypsTrue {sig : Signature} (M : Model.{u} sig) (ρ : TypeValuation.{u})
    (ν : FreeEnv M ρ) (H : Hyps) : Prop := ∀ p ∈ H, Holds M ρ ν p

def Entails {sig : Signature} (M : Model.{u} sig) (H : Hyps) (p : Tm) : Prop :=
  ∀ ρ ν, HypsTrue M ρ ν H → Holds M ρ ν p

namespace Holds

variable {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
  {ν : FreeEnv M ρ} {A : Ty} {s t p : Tm}

theorem typing (h : Holds M ρ ν p) : HasType sig [] p .bool := h.choose_spec.1.typing

theorem equal_iff : Holds M ρ ν (Tm.equal A s t) ↔
    ∃ value, Eval M ρ ν BoundEnv.empty s A value ∧ Eval M ρ ν BoundEnv.empty t A value := by
  constructor
  · rintro ⟨value, h, ht⟩
    obtain ⟨x, y, hx, hy, rfl⟩ := h.equal_inv
    have heq := (Carrier.truth_eq x y).mp ht
    cases heq
    exact ⟨x, hx, hy⟩
  · rintro ⟨value, hs, ht⟩
    exact ⟨_, hs.equal ht, (Carrier.truth_eq value value).mpr rfl⟩

theorem equal {x y : Value M ρ A} (hs : Eval M ρ ν BoundEnv.empty s A x)
    (ht : Eval M ρ ν BoundEnv.empty t A y) (h : x = y) : Holds M ρ ν (Tm.equal A s t) := by
  cases h
  exact equal_iff.mpr ⟨x, hs, ht⟩

theorem truth : Holds M ρ ν Tm.truth := ⟨_, Eval.truth, Carrier.truth_truth⟩

theorem not_falsity : ¬ Holds M ρ ν Tm.falsity := by
  rintro ⟨value, h, hv⟩
  have heq := h.unique Eval.falsity
  exact Carrier.not_truth_falsity (heq ▸ hv)

theorem tySubst_iff (hp : HasType sig [] p .bool) (σ : Nat → Ty)
    (hσ : ∀ i, (σ i).WellFormed sig.tyOps) :
    Holds M ρ ν (p.tySubst σ) ↔
      Holds M (TypeSubstitution.valuation M ρ σ) (TypeSubstitution.freeEnv σ ν) p := by
  have transfer : ∀ v,
      Eval M (TypeSubstitution.valuation M ρ σ) (TypeSubstitution.freeEnv σ ν)
        BoundEnv.empty p .bool v → Eval M ρ ν BoundEnv.empty (p.tySubst σ) .bool v := by
    intro v hv
    have hv' : Eval M (TypeSubstitution.valuation M ρ σ) (TypeSubstitution.freeEnv σ ν)
        (TypeSubstitution.boundEnv (Γ := []) σ BoundEnv.empty) p .bool v := by
      simpa using hv
    obtain ⟨v', ev, heq⟩ := hv'.tySubst_pullback hσ
    have heq' : v = v' := eq_of_heq heq
    exact heq' ▸ ev
  constructor
  · rintro ⟨v, hv, ht⟩
    obtain ⟨w, hw⟩ := hp.eval_exists M (TypeSubstitution.valuation M ρ σ)
      (TypeSubstitution.freeEnv σ ν) BoundEnv.empty
    exact ⟨w, hw, (transfer w hw |>.unique hv).symm ▸ ht⟩
  · rintro ⟨v, hv, ht⟩
    exact ⟨v, transfer v hv, ht⟩

theorem freeSubst_iff (hp : HasType sig [] p .bool) (σ : Nat → Ty → Tm)
    (μ : FreeEnv M ρ)
    (hσ : ∀ n B, B.WellFormed sig.tyOps →
      Eval M ρ ν BoundEnv.empty (σ n B) B (μ n B)) :
    Holds M ρ ν (p.freeSubst σ) ↔ Holds M ρ μ p := by
  constructor
  · rintro ⟨v, hv, ht⟩
    obtain ⟨w, hw⟩ := hp.eval_exists M ρ μ BoundEnv.empty
    exact ⟨w, hw, ((hw.freeSubst σ ν hσ).unique hv).symm ▸ ht⟩
  · rintro ⟨v, hv, ht⟩
    exact ⟨v, hv.freeSubst σ ν hσ, ht⟩

end Holds

end Silmaril.Logic.HOLLight
