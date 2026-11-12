module

public import Silmaril.Raw.SSA.Isotope.Ctx.Bound
public import Silmaril.SSA.Isotope.Types.Thms
public import Silmaril.Raw.SSA.Isotope.LetSeq.LocallyNameless.Structural

/-!
# Exact typing for sequential terms

The judgment is proposition-valued. Only product, unit, and primitive source
and target operations are needed; purity is a separate predicate.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LetSeq.LocallyNameless

variable {τ : Type u} [HasProduct τ] [HasUnit τ]
variable {ν : Type w} [DecidableEq ν]

/-- Syntax-directed typing with exact primitive source and target types. -/
inductive HasType (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) :
    {n : Nat} → BoundCtx τ n → Tm ν Φ n → τ → Prop where
  | fv {n : Nat} {β : BoundCtx τ n} {x : ν} {A : τ}
      (h : Γ.lookup x = some A) : HasType Φ Γ β (.fv x) A
  | bv {n : Nat} {β : BoundCtx τ n} {i : Fin n} :
      HasType Φ Γ β (.bv i) (β.get i)
  | op {n : Nat} {β : BoundCtx τ n} {f : Φ} {a : Tm ν Φ n}
      (ha : HasType Φ Γ β a (instrSrc f)) : HasType Φ Γ β (.op f a) (instrTrg f)
  | let₁ {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
      (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B) :
      HasType Φ Γ β (.let₁ a b) B
  | unit {n : Nat} {β : BoundCtx τ n} : HasType Φ Γ β .unit Silmaril.unit
  | pair {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A B : τ}
      (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B) :
      HasType Φ Γ β (.pair a b) (product A B)
  | let₂ {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {b : Tm ν Φ (n + 2)} {A B C : τ}
      (ha : HasType Φ Γ β a (product A B))
      (hb : HasType Φ Γ (.snoc (.snoc β A) B) b C) : HasType Φ Γ β (.let₂ a b) C

variable {Φ : Type v} [HasTy Φ τ] {Γ Γ' : Ctx ν τ} {n m : Nat}

/-- Shared, syntax-independent type-preserving bound renamings. -/
abbrev TypedRenaming {τ : Type u} {n m : Nat} (β : BoundCtx τ n) (β' : BoundCtx τ m) :=
  BoundCtx.Renaming β β'

namespace TypedRenaming
export BoundCtx.Renaming (id comp up succ underBinder underTwoBinders)
end TypedRenaming

namespace HasType

/-- Free-context transport preserves the visible type of each free name. -/
theorem weaken {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (hΓ : ∀ x A, Γ.lookup x = some A → Γ'.lookup x = some A)
    (h : HasType Φ Γ β t A) : HasType Φ Γ' β t A := by
  induction h with
  | fv h => exact .fv (hΓ _ _ h)
  | bv => exact .bv
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb

/-- Bound renaming preserves exact typing. -/
theorem rename {β : BoundCtx τ n} {β' : BoundCtx τ m} {t : Tm ν Φ n} {A : τ}
    (ρ : TypedRenaming β β') (h : HasType Φ Γ β t A) :
    HasType Φ Γ β' (Tm.rename ρ.toFun t) A := by
  induction h generalizing m with
  | fv h => exact .fv h
  | bv => exact ρ.typed _ ▸ .bv
  | op _ ih => exact .op (ih ρ)
  | let₁ _ _ iha ihb => exact .let₁ (iha ρ) (ihb (TypedRenaming.up ρ _))
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha ρ) (ihb ρ)
  | let₂ _ _ iha ihb => exact .let₂ (iha ρ) (ihb ((TypedRenaming.up ρ _).up _))

theorem renameAlong {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {ρ : Fin n → Fin m} {t : Tm ν Φ n} {A : τ}
    (hρ : BoundCtx.Ren β β' ρ) (h : HasType Φ Γ β t A) :
    HasType Φ Γ β' (Tm.rename ρ t) A := rename ⟨ρ, hρ⟩ h

theorem lift {β : BoundCtx τ n} {t : Tm ν Φ n} {A B : τ}
    (h : HasType Φ Γ β t A) : HasType Φ Γ (.snoc β B) t.lift A :=
  rename (TypedRenaming.succ β B) h

theorem underBinder {β : BoundCtx τ n} {t : Tm ν Φ (n + 1)} {A X Y : τ}
    (h : HasType Φ Γ (.snoc β Y) t A) :
    HasType Φ Γ (.snoc (.snoc β X) Y) t.underBinder A :=
  rename (TypedRenaming.underBinder β X Y) h

theorem underTwoBinders {β : BoundCtx τ n} {t : Tm ν Φ (n + 2)} {A X Y Z : τ}
    (h : HasType Φ Γ (.snoc (.snoc β Y) Z) t A) :
    HasType Φ Γ (.snoc (.snoc (.snoc β X) Y) Z) t.underTwoBinders A :=
  rename (TypedRenaming.underTwoBinders β X Y Z) h

end HasType

/-- Every bound-variable image has exactly the source variable's type. -/
def TypedSubst (β : BoundCtx τ n) (β' : BoundCtx τ m) (σ : Fin n → Tm ν Φ m) : Prop :=
  ∀ i, HasType Φ Γ β' (σ i) (β.get i)

namespace TypedSubst

theorem up {β : BoundCtx τ n} {β' : BoundCtx τ m} {σ : Fin n → Tm ν Φ m}
    (s : TypedSubst (Γ := Γ) β β' σ) (A : τ) :
    TypedSubst (Γ := Γ) (.snoc β A) (.snoc β' A) (Tm.upSub σ) :=
  Fin.cases .bv (fun i => (s i).lift)

end TypedSubst

namespace HasType

/-- Bound substitution needs exact typing of its images, independently of purity. -/
theorem bsubst {β : BoundCtx τ n} {β' : BoundCtx τ m} {σ : Fin n → Tm ν Φ m}
    (s : TypedSubst (Γ := Γ) β β' σ) {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) : HasType Φ Γ β' (Tm.bsubst σ t) A := by
  induction h generalizing m with
  | fv h => exact .fv h
  | bv => exact s _
  | op _ ih => exact .op (ih s)
  | let₁ _ _ iha ihb => exact .let₁ (iha s) (ihb (s.up _))
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair (iha s) (ihb s)
  | let₂ _ _ iha ihb => exact .let₂ (iha s) (ihb ((s.up _).up _))

theorem instantiate {β : BoundCtx τ n} {A B : τ}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (hb : HasType Φ Γ (.snoc β A) b B) (ha : HasType Φ Γ β a A) :
    HasType Φ Γ β (Tm.instantiate b a) B :=
  bsubst (σ := Fin.cases a fun i => .bv i) (Fin.cases ha fun _ => .bv) hb

/-- Replacing a free name by a term of its visible type preserves typing. -/
theorem fsubst {β : BoundCtx τ n} {t s : Tm ν Φ n} {A B : τ} {x : ν}
    (h : HasType Φ Γ β t B) (hx : Γ.lookup x = some A)
    (hs : HasType Φ Γ β s A) : HasType Φ Γ β (Tm.fsubst x s t) B := by
  induction h with
  | @fv n β y B hy =>
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

end HasType

end Silmaril.Isotope.LetSeq.LocallyNameless
