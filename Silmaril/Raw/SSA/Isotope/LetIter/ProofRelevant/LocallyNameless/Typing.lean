module

public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.LocallyNameless.Context
public import Silmaril.Raw.SSA.Isotope.Ctx.Shadowing
public import Silmaril.Raw.SSA.Isotope.Subtyping

@[expose] public section

open Silmaril.Isotope.LetIter.LocallyNameless

-- Infer indexed binders locally.
set_option autoImplicit true

namespace Silmaril.Isotope.LetIter.ProofRelevant.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν]

/-- Syntax-directed typing over a shared free context and an anonymous snoc
bound context. Derivations retain subtyping evidence in `Type`. -/
inductive HasType (Φ : Type q) [HasTy Φ τ] (Γ : Isotope.Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν Φ n → τ → Type (max u q w) where
  | fv (h : Γ.lookup x = some A) : HasType Φ Γ β (.fv x) A
  | bv : HasType Φ Γ β (.bv ι) (β.get ι)
  | op (ha : HasType Φ Γ β a (instrSrc f)) : HasType Φ Γ β (.op f a) (instrTrg f)
  | let₁ (ha : HasType Φ Γ β a A)
      (hb : HasType Φ Γ (.snoc β A) b B) : HasType Φ Γ β (.let₁ a b) B
  | unit : HasType Φ Γ β .unit Silmaril.unit
  | pair (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B) :
      HasType Φ Γ β (.pair a b) (Silmaril.product A B)
  | let₂ (ha : HasType Φ Γ β a (Silmaril.product A B))
      (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) : HasType Φ Γ β (.let₂ a c) C
  | inl (ha : HasType Φ Γ β a A) : HasType Φ Γ β (.inl a) (Silmaril.coprod A B)
  | inr (hb : HasType Φ Γ β b B) : HasType Φ Γ β (.inr b) (Silmaril.coprod A B)
  | case (he : HasType Φ Γ β e (Silmaril.coprod A B))
      (hl : HasType Φ Γ (.snoc β A) l C)
      (hr : HasType Φ Γ (.snoc β B) r C) : HasType Φ Γ β (.case e l r) C
  | abort (ha : HasType Φ Γ β a Silmaril.empty) : HasType Φ Γ β (.abort a) C
  | iter (ha : HasType Φ Γ β a A)
      (hb : HasType Φ Γ (.snoc β A) b (Silmaril.coprod B A)) :
      HasType Φ Γ β (.iter a b) B
  | sub (ha : HasType Φ Γ β a A) (hAB : Subty A B) : HasType Φ Γ β a B

namespace HasType

variable {Φ : Type q} [HasTy Φ τ] {Γ Γ' : Isotope.Ctx ν τ} {β β' : BoundCtx τ n}
  {t : Tm ν Φ n} {A B : τ}

def weakenSame (wΓ : FreeWk Γ' Γ) :
    {n : Nat} → {β β' : BoundCtx τ n} → BoundCtx.Wk β' β →
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A → HasType Φ Γ' β' t A
  | _, _, _, _wβ, _, _, .fv h =>
      let ⟨_B, hB, hBA⟩ := wΓ.lookup _ _ h
      .sub (.fv hB) hBA
  | _, _, _, wβ, _, _, .bv => .sub .bv (wβ.at _)
  | _, _, _, wβ, _, _, .op ha => .op (weakenSame wΓ wβ ha)
  | _, _, _, wβ, _, _, .let₁ ha hb => .let₁ (weakenSame wΓ wβ ha)
      (weakenSame wΓ (.snoc wβ (Subty.refl _)) hb)
  | _, _, _, _, _, _, .unit => .unit
  | _, _, _, wβ, _, _, .pair ha hb => .pair (weakenSame wΓ wβ ha) (weakenSame wΓ wβ hb)
  | _, _, _, wβ, _, _, .let₂ ha hc => .let₂ (weakenSame wΓ wβ ha)
      (weakenSame wΓ (.snoc (.snoc wβ (Subty.refl _)) (Subty.refl _)) hc)
  | _, _, _, wβ, _, _, .inl ha => .inl (weakenSame wΓ wβ ha)
  | _, _, _, wβ, _, _, .inr hb => .inr (weakenSame wΓ wβ hb)
  | _, _, _, wβ, _, _, .case he hl hr => .case (weakenSame wΓ wβ he)
      (weakenSame wΓ (.snoc wβ (Subty.refl _)) hl)
      (weakenSame wΓ (.snoc wβ (Subty.refl _)) hr)
  | _, _, _, wβ, _, _, .abort ha => .abort (weakenSame wΓ wβ ha)
  | _, _, _, wβ, _, _, .iter ha hb => .iter (weakenSame wΓ wβ ha)
      (weakenSame wΓ (.snoc wβ (Subty.refl _)) hb)
  | _, _, _, wβ, _, _, .sub ha hAB => .sub (weakenSame wΓ wβ ha) hAB

/-- Proof-relevant weakening, with a separately supplied result coercion. -/
def weaken (wΓ : FreeWk Γ' Γ) (wβ : BoundCtx.Wk β' β)
    (hAB : Subty A B) : HasType Φ Γ β t A → HasType Φ Γ' β' t B :=
  fun h => .sub (weakenSame wΓ wβ h) hAB

/-- Proposition-truncated existence of a weakened typing derivation. -/
theorem weaken_nonempty (wΓ : FreeWkProp Γ' Γ)
    (wβ : BoundCtx.WkProp β' β) (hAB : Nonempty (Subty A B))
    (h : Nonempty (HasType Φ Γ β t A)) : Nonempty (HasType Φ Γ' β' t B) :=
  wΓ.elim fun fΓ => wβ.elim fun fβ => hAB.elim fun fAB => h.elim fun ht =>
    ⟨weaken fΓ fβ fAB ht⟩

/-- Exact transport along a shared shadow-only name edit. -/
def shadow (d : Ctx.ShadowEdit Γ Γ') :
    {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
    HasType Φ Γ β t A → HasType Φ Γ' β t A
  | _, _, _, _, .fv h => .fv (by rw [← d.lookup_eq]; exact h)
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op ha => .op (shadow d ha)
  | _, _, _, _, .let₁ ha hb => .let₁ (shadow d ha) (shadow d hb)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair ha hb => .pair (shadow d ha) (shadow d hb)
  | _, _, _, _, .let₂ ha hc => .let₂ (shadow d ha) (shadow d hc)
  | _, _, _, _, .inl ha => .inl (shadow d ha)
  | _, _, _, _, .inr hb => .inr (shadow d hb)
  | _, _, _, _, .case he hl hr => .case (shadow d he) (shadow d hl) (shadow d hr)
  | _, _, _, _, .abort ha => .abort (shadow d ha)
  | _, _, _, _, .iter ha hb => .iter (shadow d ha) (shadow d hb)
  | _, _, _, _, .sub ha hAB => .sub (shadow d ha) hAB

end HasType

end Silmaril.Isotope.LetIter.ProofRelevant.LocallyNameless
