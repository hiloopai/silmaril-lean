module

public import Silmaril.Logic.HOLLight.Semantics.Term

@[expose] public section

namespace Silmaril.Logic.HOLLight

universe u

namespace Eval

theorem rename {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {ν : FreeEnv M ρ} {Γ : List Ty} {η : BoundEnv M ρ Γ}
    {t : Tm} {A : Ty} {value : Value M ρ A} (h : Eval M ρ ν η t A value)
    {Δ : List Ty} (r : Nat → Nat) (ξ : BoundEnv M ρ Δ)
    (hΓ : ∀ i B, Γ[i]? = some B → Δ[r i]? = some B)
    (hη : ∀ i B hi, ξ (r i) B (hΓ i B hi) = η i B hi) :
    Eval M ρ ν ξ (t.rename r) A value := by
  induction h generalizing Δ r with
  | bvar η hi hA =>
    simpa only [Tm.rename, hη _ _ hi] using Eval.bvar (ν := ν) ξ (hΓ _ _ hi) hA
  | fvar η n hA => exact .fvar ξ n hA
  | const η hc => exact .const ξ hc
  | app hf hx ihf ihx => exact .app (ihf r ξ hΓ hη) (ihx r ξ hΓ hη)
  | @lam Γ η A B body hA f hb ih =>
    apply Eval.lam hA
    intro x
    have hΓ' : ∀ i C, (A :: Γ)[i]? = some C →
        (A :: Δ)[DeBruijn.lift r i]? = some C := by
      intro i C hi
      cases i with
      | zero => exact hi
      | succ i => exact hΓ i C hi
    apply ih x (DeBruijn.lift r) (ξ.extend x) hΓ'
    intro i C hi
    cases i with
    | zero =>
      have same : A = C := Option.some.inj hi
      cases same
      rfl
    | succ i => exact hη i C hi

theorem weaken {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {ν : FreeEnv M ρ} {Γ : List Ty} {η : BoundEnv M ρ Γ}
    {t : Tm} {A B : Ty} {value : Value M ρ A} (h : Eval M ρ ν η t A value)
    (x : Value M ρ B) : Eval M ρ ν (η.extend x) t.weaken A value :=
  h.rename Nat.succ (η.extend x) (fun _ _ hi => hi) (fun _ _ _ => rfl)

/-- A locally closed term can be evaluated in any ambient bound environment. -/
theorem closed_context {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {ν : FreeEnv M ρ} {t : Tm} {A : Ty} {value : Value M ρ A}
    (h : Eval M ρ ν BoundEnv.empty t A value) {Γ : List Ty} (η : BoundEnv M ρ Γ) :
    Eval M ρ ν η t A value := by
  simpa only [Tm.rename_id] using h.rename id η (by intro i B hi; simp at hi)
    (by intro i B hi; simp at hi)

theorem subst {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {ν : FreeEnv M ρ} {Γ : List Ty} {η : BoundEnv M ρ Γ}
    {t : Tm} {A : Ty} {value : Value M ρ A} (h : Eval M ρ ν η t A value)
    {Δ : List Ty} (σ : Nat → Tm) (ξ : BoundEnv M ρ Δ)
    (hσ : ∀ i B (hi : Γ[i]? = some B), B.WellFormed sig.tyOps →
      Eval M ρ ν ξ (σ i) B (η i B hi)) :
    Eval M ρ ν ξ (t.subst σ) A value := by
  induction h generalizing Δ σ with
  | bvar η hi hA => exact hσ _ _ hi hA
  | fvar η n hA => exact .fvar ξ n hA
  | const η hc => exact .const ξ hc
  | app hf hx ihf ihx => exact .app (ihf σ ξ hσ) (ihx σ ξ hσ)
  | @lam Γ η A B body hA f hb ih =>
    apply Eval.lam hA
    intro x
    apply ih x (Tm.liftSub σ) (ξ.extend x)
    intro i C hi hC
    cases i with
    | zero =>
      have same : A = C := Option.some.inj hi
      cases same
      exact .bvar (ξ.extend x) rfl hC
    | succ i => exact (hσ i C hi hC).weaken x

theorem «open» {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {ν : FreeEnv M ρ} {Γ : List Ty} {η : BoundEnv M ρ Γ}
    {body argument : Tm} {A B : Ty} {x : Value M ρ A} {y : Value M ρ B}
    (hb : Eval M ρ ν (η.extend x) body B y) (hx : Eval M ρ ν η argument A x) :
    Eval M ρ ν η (body.open argument) B y := by
  apply hb.subst (Tm.openSub argument) η
  intro i C hi hC
  cases i with
  | zero =>
    have same : A = C := Option.some.inj hi
    cases same
    exact hx
  | succ i => exact .bvar η hi hC

/-- Free substitution changes the valuation by the denotations of its replacements. -/
theorem freeSubst {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {ν : FreeEnv M ρ} {Γ : List Ty} {η : BoundEnv M ρ Γ}
    {t : Tm} {A : Ty} {value : Value M ρ A} (h : Eval M ρ ν η t A value)
    (σ : Nat → Ty → Tm) (μ : FreeEnv M ρ)
    (hσ : ∀ n B, B.WellFormed sig.tyOps → Eval M ρ μ η (σ n B) B (ν n B)) :
    Eval M ρ μ η (t.freeSubst σ) A value := by
  induction h generalizing σ with
  | bvar η hi hA => exact .bvar η hi hA
  | fvar η n hA => exact hσ n _ hA
  | const η hc => exact .const η hc
  | app hf hx ihf ihx => exact .app (ihf σ hσ) (ihx σ hσ)
  | lam hA hb ih =>
    apply Eval.lam hA
    intro x
    exact ih x _ (fun n B hB => (hσ n B hB).weaken x)

/-- Denotation only depends on the finite free support. -/
theorem congr_free {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {ν : FreeEnv M ρ} {Γ : List Ty} {η : BoundEnv M ρ Γ}
    {t : Tm} {A : Ty} {value : Value M ρ A} (h : Eval M ρ ν η t A value)
    (μ : FreeEnv M ρ) (hν : ∀ n B, (n, B) ∈ t.freeVars → μ n B = ν n B) :
    Eval M ρ μ η t A value := by
  induction h with
  | bvar η hi hA => exact .bvar η hi hA
  | fvar η n hA =>
    rw [← hν n _ (by simp [Tm.freeVars])]
    exact .fvar η n hA
  | const η hc => exact .const η hc
  | app hf hx ihf ihx =>
    exact .app (ihf (fun n B hn => hν n B (List.mem_append_left _ hn)))
      (ihx (fun n B hn => hν n B (List.mem_append_right _ hn)))
  | lam hA hb ih => exact .lam hA (fun x => ih x hν)

end Eval

namespace FreeEnv

/-- Update a typed free name, preserving all other valuation components. -/
def update {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    (ν : FreeEnv M ρ) (name : Nat) (A : Ty) (value : Value M ρ A) : FreeEnv M ρ :=
  fun n B => if h : (n, B) = (name, A) then
    (by have same : B = A := congrArg Prod.snd h; cases same; exact value) else ν n B

@[simp] theorem update_self {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    (ν : FreeEnv M ρ) (name : Nat) (A : Ty) (value : Value M ρ A) :
    update ν name A value name A = value := by simp [update]

theorem update_other {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    (ν : FreeEnv M ρ) (name : Nat) (A : Ty) (value : Value M ρ A)
    {n : Nat} {B : Ty} (h : (n, B) ≠ (name, A)) :
    update ν name A value n B = ν n B := by simp [update, h]

end FreeEnv

namespace Eval

theorem update_fresh {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {ν : FreeEnv M ρ} {Γ : List Ty} {η : BoundEnv M ρ Γ}
    {t : Tm} {A B : Ty} {value : Value M ρ B} (h : Eval M ρ ν η t B value)
    (name : Nat) (x : Value M ρ A) (hfresh : t.Fresh (name, A)) :
    Eval M ρ (ν.update name A x) η t B value := by
  apply h.congr_free
  intro n C hn
  exact FreeEnv.update_other _ _ _ _ (fun heq => hfresh (heq ▸ hn))

/-- Named abstraction is interpreted by varying exactly its typed free variable. -/
theorem abstractFree {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
    {ν : FreeEnv M ρ} {t : Tm} {A B : Ty} {value : Value M ρ B}
    (name : Nat) (x : Value M ρ A)
    (h : Eval M ρ (ν.update name A x) BoundEnv.empty t B value) :
    Eval M ρ ν (BoundEnv.empty.extend x) (t.replaceFree (name, A) (.bvar 0)) B value := by
  apply (h.closed_context (BoundEnv.empty.extend x)).freeSubst _ ν
  intro n C hC
  by_cases heq : (n, C) = (name, A)
  · have hn : n = name := congrArg Prod.fst heq
    have hCA : C = A := congrArg Prod.snd heq
    cases hn
    cases hCA
    simp only [↓reduceIte, FreeEnv.update_self]
    exact Eval.bvar (M := M) (ρ := ρ) (ν := ν) (i := 0) (BoundEnv.empty.extend x) rfl hC
  · simpa only [heq, ↓reduceIte, FreeEnv.update_other _ _ _ _ heq] using
      Eval.fvar (M := M) (ρ := ρ) (ν := ν) (BoundEnv.empty.extend x) n hC

end Eval
end Silmaril.Logic.HOLLight
