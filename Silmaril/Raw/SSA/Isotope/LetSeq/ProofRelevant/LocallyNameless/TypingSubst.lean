module

public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.Typing

@[expose] public section

open Silmaril.Isotope.LetSeq.LocallyNameless

-- Infer indexed binders locally.
set_option autoImplicit true

/-!
# Proof-relevant renaming and substitution of typing derivations

Typing derivations retain subtyping evidence, so substitution returns a
specific derivation rather than merely proving that some derivation exists.
-/

namespace Silmaril.Isotope.LetSeq.ProofRelevant.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {Γ : Isotope.Ctx ν τ}



namespace HasType

def newest {n : Nat} {β : BoundCtx τ n} {A : τ} :
    HasType Φ Γ (.snoc β A) (.bv 0) A := by
  simpa [BoundCtx.get] using
    (HasType.bv (Φ := Φ) (Γ := Γ) (β := .snoc β A) (ι := (0 : Fin (n + 1))))

def previous {n : Nat} {β : BoundCtx τ n} {A B : τ} :
    HasType Φ Γ (.snoc (.snoc β A) B) (.bv 1) A := by
  simpa only [Fin.succ_zero_eq_one] using
    (show HasType Φ Γ (.snoc (.snoc β A) B) (.bv (Fin.succ 0)) A from .bv)

/-- Rename a typing derivation along a type-preserving index map. -/
def rename {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    (ρ : TypedRenaming β β') :
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      HasType Φ Γ β' (t.rename ρ.toFun) A
  | _, _, .fv h => .fv h
  | _, _, .bv (ι := i) => ρ.typed i ▸ .bv
  | _, _, .op h => .op (rename ρ h)
  | _, _, .let₁ ha hb => .let₁ (rename ρ ha) (rename (TypedRenaming.up ρ _) hb)
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair (rename ρ ha) (rename ρ hb)
  | _, _, .let₂ ha hb => .let₂ (rename ρ ha) (rename (TypedRenaming.up (TypedRenaming.up ρ _) _) hb)
  | _, _, .sub h d => .sub (rename ρ h) d

/-- Insert a newest bound variable into a typing derivation. -/
def lift {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A B : τ}
    (h : HasType Φ Γ β t A) :
    HasType Φ Γ (.snoc β B) t.lift A :=
  rename (TypedRenaming.succ β B) h

def underBinder {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ (n + 1)}
    {A X Y : τ} (h : HasType Φ Γ (.snoc β Y) t A) :
    HasType Φ Γ (.snoc (.snoc β X) Y) t.underBinder A :=
  rename (TypedRenaming.underBinder β X Y) h

def underTwoBinders {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ (n + 2)}
    {A X Y Z : τ} (h : HasType Φ Γ (.snoc (.snoc β Y) Z) t A) :
    HasType Φ Γ (.snoc (.snoc (.snoc β X) Y) Z) t.underTwoBinders A :=
  rename (TypedRenaming.underTwoBinders β X Y Z) h

end HasType

/-- A simultaneous, proof-relevant substitution for every bound variable. -/
def TypedSubst (β : BoundCtx τ n) (β' : BoundCtx τ m)
    (σ : Fin n → Tm ν Φ m) : Type (max u q w) :=
  (i : Fin n) → HasType Φ Γ β' (σ i) (β.get i)

namespace TypedSubst

def up {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : TypedSubst (Γ := Γ) β β' σ) (A : τ) :
    TypedSubst (Γ := Γ) (.snoc β A) (.snoc β' A)
      (fun i => Fin.cases (.bv (0 : Fin (m + 1))) (fun j => (σ j).lift) i) :=
  Fin.cases (.bv) (fun i => (s i).lift)

end TypedSubst

namespace HasType

/-- Simultaneous substitution on typing derivations. -/
def bsubst {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : TypedSubst (Γ := Γ) β β' σ) :
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      HasType Φ Γ β' (t.bsubst σ) A
  | _, _, .fv h => .fv h
  | _, _, .bv (ι := i) => s i
  | _, _, .op h => .op (bsubst s h)
  | _, _, .let₁ ha hb => .let₁ (bsubst s ha) (bsubst (s.up _) hb)
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair (bsubst s ha) (bsubst s hb)
  | _, _, .let₂ ha hb => .let₂ (bsubst s ha) (bsubst ((s.up _).up _) hb)
  | _, _, .sub h d => .sub (bsubst s h) d

/-- Open the newest binder with a specifically typed term. -/
def instantiate {n : Nat} {β : BoundCtx τ n} {A B : τ}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (hb : HasType Φ Γ (.snoc β A) b B)
    (ha : HasType Φ Γ β a A) :
    HasType Φ Γ β (Tm.instantiate b a) B :=
  bsubst (σ := Fin.cases a fun i => .bv i) (Fin.cases ha fun _ => .bv) hb

end HasType

end Silmaril.Isotope.LetSeq.ProofRelevant.LocallyNameless
