module

public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Typing
public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Algebra

@[expose] public section
set_option autoImplicit true

/-!
# Locally nameless metatheory without subtyping

Bound renamings and simultaneous substitutions carry exact type preservation.
No coercion cases or subtyping coherence hypotheses occur in these proofs.
-/

namespace Silmaril.Isotope.LetCase.LocallyNameless

variable {τ : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {Γ Γ' : Isotope.Ctx ν τ}

/-- A bound-variable renaming preserving the type at every selected slot. -/
abbrev TypedRenaming (β : BoundCtx τ n) (β' : BoundCtx τ m) := BoundCtx.Renaming β β'

namespace TypedRenaming
export BoundCtx.Renaming (id comp up succ underBinder underTwoBinders)
end TypedRenaming

namespace HasType

theorem newest {n : Nat} {β : BoundCtx τ n} {A : τ} :
    HasType Φ Γ (.snoc β A) (.bv 0) A := .bv

theorem previous {n : Nat} {β : BoundCtx τ n} {A B : τ} :
    HasType Φ Γ (.snoc (.snoc β A) B) (.bv 1) A := .bv

/-- Typing is preserved by every exactly typed bound renaming. -/
theorem rename {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    (ρ : TypedRenaming β β') :
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      HasType Φ Γ β' (Tm.rename ρ.toFun t) A
  | _, _, .fv h => .fv h
  | _, _, .bv (ι := i) => ρ.typed i ▸ .bv
  | _, _, .op h => .op (rename ρ h)
  | _, _, .let₁ ha hb => .let₁ (rename ρ ha) (rename (TypedRenaming.up ρ _) hb)
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair (rename ρ ha) (rename ρ hb)
  | _, _, .let₂ ha hb => .let₂ (rename ρ ha) (rename (TypedRenaming.up (TypedRenaming.up ρ _) _) hb)
  | _, _, .inl h => .inl (rename ρ h)
  | _, _, .inr h => .inr (rename ρ h)
  | _, _, .case he hl hr =>
      .case (rename ρ he) (rename (TypedRenaming.up ρ _) hl) (rename (TypedRenaming.up ρ _) hr)
  | _, _, .abort h => .abort (rename ρ h)

theorem lift {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A B : τ}
    (h : HasType Φ Γ β t A) :
    HasType Φ Γ (.snoc β B) (Tm.lift t) A :=
  rename (TypedRenaming.succ β B) h

theorem underBinder {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ (n + 1)}
    {A X Y : τ} (h : HasType Φ Γ (.snoc β Y) t A) :
    HasType Φ Γ (.snoc (.snoc β X) Y)
      (Tm.underBinder t) A :=
  rename (TypedRenaming.underBinder β X Y) h

theorem underTwoBinders {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ (n + 2)}
    {A X Y Z : τ} (h : HasType Φ Γ (.snoc (.snoc β Y) Z) t A) :
    HasType Φ Γ (.snoc (.snoc (.snoc β X) Y) Z)
      (Tm.underTwoBinders t) A :=
  rename (TypedRenaming.underTwoBinders β X Y Z) h

end HasType

/-- A simultaneous substitution supplying an exactly typed image for each
bound variable. -/
def TypedSubst (β : BoundCtx τ n) (β' : BoundCtx τ m)
    (σ : Fin n → Tm ν Φ m) : Prop :=
  (i : Fin n) → HasType Φ Γ β' (σ i) (β.get i)

namespace TypedSubst

theorem up {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : TypedSubst (Γ := Γ) β β' σ) (A : τ) :
    TypedSubst (Γ := Γ) (.snoc β A) (.snoc β' A)
      (fun i => Fin.cases (.bv (0 : Fin (m + 1)))
        (fun j => Tm.lift (σ j)) i) :=
  Fin.cases (.bv) (fun i => (s i).lift)

end TypedSubst

namespace HasType

/-- Typing is preserved by simultaneous bound substitution. -/
theorem bsubst {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : TypedSubst (Γ := Γ) β β' σ) :
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      HasType Φ Γ β'
        (Tm.bsubst σ t) A
  | _, _, .fv h => .fv h
  | _, _, .bv (ι := i) => s i
  | _, _, .op h => .op (bsubst s h)
  | _, _, .let₁ ha hb => .let₁ (bsubst s ha) (bsubst (s.up _) hb)
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair (bsubst s ha) (bsubst s hb)
  | _, _, .let₂ ha hb => .let₂ (bsubst s ha) (bsubst ((s.up _).up _) hb)
  | _, _, .inl h => .inl (bsubst s h)
  | _, _, .inr h => .inr (bsubst s h)
  | _, _, .case he hl hr =>
      .case (bsubst s he) (bsubst (s.up _) hl) (bsubst (s.up _) hr)
  | _, _, .abort h => .abort (bsubst s h)

/-- Opening the newest binder preserves typing. -/
theorem instantiate {n : Nat} {β : BoundCtx τ n} {A B : τ}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (hb : HasType Φ Γ (.snoc β A) b B) (ha : HasType Φ Γ β a A) :
    HasType Φ Γ β (Tm.instantiate b a) B :=
  bsubst (σ := Fin.cases a fun i => .bv i) (Fin.cases ha fun _ => .bv) hb

/-- Replacing a free name by a term of its visible type preserves typing. -/
theorem fsubst {β : BoundCtx τ n} {t s : Tm ν Φ n} {A B : τ} {x : ν}
    (h : HasType Φ Γ β t B) (hx : Γ.lookup x = some A)
    (hs : HasType Φ Γ β s A) : HasType Φ Γ β (Tm.fsubst x s t) B := by
  induction h with
  | @fv y B n β hy =>
      by_cases hxy : x = y
      · subst y
        have hab : A = B := Option.some.inj (hx.symm.trans hy)
        subst B
        simpa [Tm.fsubst] using hs
      · simpa [Tm.fsubst, hxy] using (HasType.fv hy : HasType Φ Γ β (.fv y) B)
  | bv => exact .bv
  | op _ ih => exact .op (ih hs)
  | let₁ _ _ iha ihb => exact .let₁ (iha hs) (ihb hs.lift)
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha hs) (ihb hs)
  | let₂ _ _ iha ihb => exact .let₂ (iha hs) (ihb hs.lift.lift)

  | inl _ ih => exact .inl (ih hs)
  | inr _ ih => exact .inr (ih hs)
  | case _ _ _ ihe ihl ihr => exact .case (ihe hs) (ihl hs.lift) (ihr hs.lift)
  | abort _ ih => exact .abort (ih hs)

end HasType

end Silmaril.Isotope.LetCase.LocallyNameless
