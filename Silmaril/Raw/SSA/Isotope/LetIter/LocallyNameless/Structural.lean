module

public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Typing

/-!
# Renaming and substitution for exact let-iter

Typing preservation below uses only exact type equality.
-/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.LetIter.LocallyNameless

namespace Tm

variable {ν : Type w} {Φ : Type v} {n m k : Nat}

@[simp] theorem up_id : up (fun i : Fin n => i) = fun i => i := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem up_comp (ρ : Fin n → Fin m) (σ : Fin m → Fin k) :
    up (fun i => σ (ρ i)) = fun i => up σ (up ρ i) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem rename_id (t : Tm ν Φ n) : rename (fun i => i) t = t := by
  induction t <;> simp_all [rename]

theorem rename_comp (ρ : Fin n → Fin m) (σ : Fin m → Fin k) (t : Tm ν Φ n) :
    rename σ (rename ρ t) = rename (fun i => σ (ρ i)) t := by
  induction t generalizing m k <;> simp_all [rename, ← up_comp]

theorem rename_congr {ρ σ : Fin n → Fin m} (h : ∀ i, ρ i = σ i) (t : Tm ν Φ n) :
    rename ρ t = rename σ t := congrArg (fun f => rename f t) (funext h)

theorem bsubst_congr {σ θ : Fin n → Tm ν Φ m} (h : ∀ i, σ i = θ i) (t : Tm ν Φ n) :
    bsubst σ t = bsubst θ t := congrArg (fun f => bsubst f t) (funext h)

@[simp] theorem rename_lift (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    rename (up ρ) t.lift = (rename ρ t).lift := by
  rw [lift, rename_comp, lift, rename_comp]
  rfl

theorem rename_upSub (ρ : Fin m → Fin k) (σ : Fin n → Tm ν Φ m) :
    (fun i => rename (up ρ) (upSub σ i)) = upSub (fun i => rename ρ (σ i)) := by
  funext i
  exact Fin.cases rfl (fun j => rename_lift ρ (σ j)) i

theorem rename_bsubst (ρ : Fin m → Fin k) (σ : Fin n → Tm ν Φ m) (t : Tm ν Φ n) :
    rename ρ (bsubst σ t) = bsubst (fun i => rename ρ (σ i)) t := by
  induction t generalizing m k <;> simp_all [bsubst, rename, rename_upSub]

theorem upSub_comp_ren (σ : Fin m → Tm ν Φ k) (ρ : Fin n → Fin m) :
    (fun i => upSub σ (up ρ i)) = upSub (fun i => σ (ρ i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem bsubst_rename (σ : Fin m → Tm ν Φ k) (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    bsubst σ (rename ρ t) = bsubst (fun i => σ (ρ i)) t := by
  induction t generalizing m k <;> simp_all [bsubst, rename, upSub_comp_ren]

@[simp] theorem bsubst_lift (σ : Fin n → Tm ν Φ m) (t : Tm ν Φ n) :
    bsubst (upSub σ) t.lift = (bsubst σ t).lift := by
  rw [lift, bsubst_rename, lift, rename_bsubst]
  rfl

theorem upSub_comp (σ : Fin n → Tm ν Φ m) (θ : Fin m → Tm ν Φ k) :
    (fun i => bsubst (upSub θ) (upSub σ i)) = upSub (fun i => bsubst θ (σ i)) := by
  funext i
  exact Fin.cases rfl (fun j => bsubst_lift θ (σ j)) i

theorem bsubst_comp (θ : Fin m → Tm ν Φ k) (σ : Fin n → Tm ν Φ m) (t : Tm ν Φ n) :
    bsubst θ (bsubst σ t) = bsubst (fun i => bsubst θ (σ i)) t := by
  induction t generalizing m k <;> simp_all [bsubst, upSub_comp]

theorem upSub_bv (ρ : Fin n → Fin m) :
    upSub (fun i => .bv (ρ i) : Fin n → Tm ν Φ m) = fun i => .bv (up ρ i) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem bsubst_bv_eq_rename (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    bsubst (fun i => .bv (ρ i)) t = rename ρ t := by
  induction t generalizing m <;> simp_all [bsubst, rename, upSub_bv]

@[simp] theorem bsubst_id (t : Tm ν Φ n) : bsubst .bv t = t := by
  rw [bsubst_bv_eq_rename (fun i => i), rename_id]

end Tm

/-- The shared bound-context renaming bundle, with no term-syntax dependency. -/
abbrev TypedRenaming {τ : Type u} {n m : Nat} (β : BoundCtx τ n) (β' : BoundCtx τ m) :=
  BoundCtx.Renaming β β'

namespace TypedRenaming
export BoundCtx.Renaming (id comp up succ underBinder underTwoBinders)
end TypedRenaming

section Typing

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Isotope.Ctx ν τ}

namespace HasType

theorem newest {n : Nat} {β : BoundCtx τ n} {A : τ} :
    HasType Φ Γ (.snoc β A) (.bv 0) A := .bv

theorem previous {n : Nat} {β : BoundCtx τ n} {A B : τ} :
    HasType Φ Γ (.snoc (.snoc β A) B) (.bv 1) A := .bv

/-- Rename along an exactly type-preserving bound-variable map. -/
theorem rename {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    (ρ : TypedRenaming β β') :
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
      HasType Φ Γ β' (t.rename ρ.toFun) A
  | _, _, .fv h => .fv h
  | _, _, .bv (ι := i) => ρ.typed i ▸ .bv
  | _, _, .op h => .op (rename ρ h)
  | _, _, .let₁ ha hb => .let₁ (rename ρ ha) (rename (TypedRenaming.up ρ _) hb)
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair (rename ρ ha) (rename ρ hb)
  | _, _, .let₂ ha hb =>
      .let₂ (rename ρ ha) (rename (TypedRenaming.up (TypedRenaming.up ρ _) _) hb)
  | _, _, .inl h => .inl (rename ρ h)
  | _, _, .inr h => .inr (rename ρ h)
  | _, _, .case he hl hr =>
      .case (rename ρ he) (rename (TypedRenaming.up ρ _) hl) (rename (TypedRenaming.up ρ _) hr)
  | _, _, .abort h => .abort (rename ρ h)
  | _, _, .iter ha hb => .iter (rename ρ ha) (rename (TypedRenaming.up ρ _) hb)

theorem renameAlong {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {ρ : Fin n → Fin m} (hρ : BoundCtx.Ren β β' ρ)
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) :
    HasType Φ Γ β' (t.rename ρ) A := rename ⟨ρ, hρ⟩ h

theorem lift {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A B : τ}
    (h : HasType Φ Γ β t A) : HasType Φ Γ (.snoc β B) t.lift A :=
  rename (.succ β B) h

theorem underBinder {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ (n + 1)} {A X Y : τ}
    (h : HasType Φ Γ (.snoc β Y) t A) :
    HasType Φ Γ (.snoc (.snoc β X) Y) t.underBinder A :=
  rename (.underBinder β X Y) h

theorem underTwoBinders {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ (n + 2)} {A X Y Z : τ}
    (h : HasType Φ Γ (.snoc (.snoc β Y) Z) t A) :
    HasType Φ Γ (.snoc (.snoc (.snoc β X) Y) Z) t.underTwoBinders A :=
  rename (.underTwoBinders β X Y Z) h

end HasType

/-- Every image of a simultaneous substitution has exactly its source slot's type. -/
def TypedSubst {n m : Nat} (β : BoundCtx τ n) (β' : BoundCtx τ m)
    (σ : Fin n → Tm ν Φ m) : Prop := ∀ i, HasType Φ Γ β' (σ i) (β.get i)

namespace TypedSubst

theorem up {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : TypedSubst (Γ := Γ) β β' σ) (A : τ) :
    TypedSubst (Γ := Γ) (.snoc β A) (.snoc β' A) (Tm.upSub σ) :=
  Fin.cases .bv (fun i => (s i).lift)

end TypedSubst

namespace HasType

/-- Exact typing is preserved by simultaneous bound substitution. -/
theorem bsubst {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : TypedSubst (Γ := Γ) β β' σ) :
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A → HasType Φ Γ β' (t.bsubst σ) A
  | _, _, .fv h => .fv h
  | _, _, .bv (ι := i) => s i
  | _, _, .op h => .op (bsubst s h)
  | _, _, .let₁ ha hb => .let₁ (bsubst s ha) (bsubst (s.up _) hb)
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair (bsubst s ha) (bsubst s hb)
  | _, _, .let₂ ha hb => .let₂ (bsubst s ha) (bsubst ((s.up _).up _) hb)
  | _, _, .inl h => .inl (bsubst s h)
  | _, _, .inr h => .inr (bsubst s h)
  | _, _, .case he hl hr => .case (bsubst s he) (bsubst (s.up _) hl) (bsubst (s.up _) hr)
  | _, _, .abort h => .abort (bsubst s h)
  | _, _, .iter ha hb => .iter (bsubst s ha) (bsubst (s.up _) hb)

theorem instantiate {n : Nat} {β : BoundCtx τ n} {A B : τ}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (hb : HasType Φ Γ (.snoc β A) b B) (ha : HasType Φ Γ β a A) :
    HasType Φ Γ β (Tm.instantiate b a) B :=
  bsubst (σ := Fin.cases a fun i => .bv i) (Fin.cases ha fun _ => .bv) hb

end HasType
end Typing

section Purity

variable {ν : Type w} {Φ : Type v} {ε : Type r} [HasEff Φ ε] {pureEff : ε}

namespace Pure

theorem rename {n m : Nat} (ρ : Fin n → Fin m) :
    {t : Tm ν Φ n} → Pure pureEff t → Pure pureEff (t.rename ρ)
  | _, .fv => .fv
  | _, .bv => .bv
  | _, .op hf ha => .op hf (rename ρ ha)
  | _, .let₁ ha hb => .let₁ (rename ρ ha) (rename (Tm.up ρ) hb)
  | _, .unit => .unit
  | _, .pair ha hb => .pair (rename ρ ha) (rename ρ hb)
  | _, .let₂ ha hb => .let₂ (rename ρ ha) (rename (Tm.up (Tm.up ρ)) hb)
  | _, .inl h => .inl (rename ρ h)
  | _, .inr h => .inr (rename ρ h)
  | _, .case he hl hr => .case (rename ρ he) (rename (Tm.up ρ) hl) (rename (Tm.up ρ) hr)
  | _, .abort h => .abort (rename ρ h)

theorem lift {n : Nat} {t : Tm ν Φ n} (h : Pure pureEff t) : Pure pureEff t.lift :=
  rename Fin.succ h

theorem upSub {n m : Nat} {σ : Fin n → Tm ν Φ m} (hσ : ∀ i, Pure pureEff (σ i)) :
    ∀ i, Pure pureEff (Tm.upSub σ i) := Fin.cases .bv (fun i => (hσ i).lift)

theorem bsubst {n m : Nat} {σ : Fin n → Tm ν Φ m} (hσ : ∀ i, Pure pureEff (σ i)) :
    {t : Tm ν Φ n} → Pure pureEff t → Pure pureEff (t.bsubst σ)
  | _, .fv => .fv
  | _, .bv => hσ _
  | _, .op hf ha => .op hf (bsubst hσ ha)
  | _, .let₁ ha hb => .let₁ (bsubst hσ ha) (bsubst (upSub hσ) hb)
  | _, .unit => .unit
  | _, .pair ha hb => .pair (bsubst hσ ha) (bsubst hσ hb)
  | _, .let₂ ha hb => .let₂ (bsubst hσ ha) (bsubst (upSub (upSub hσ)) hb)
  | _, .inl h => .inl (bsubst hσ h)
  | _, .inr h => .inr (bsubst hσ h)
  | _, .case he hl hr =>
      .case (bsubst hσ he) (bsubst (upSub hσ) hl) (bsubst (upSub hσ) hr)
  | _, .abort h => .abort (bsubst hσ h)

theorem instantiate {n : Nat} {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (hb : Pure pureEff b) (ha : Pure pureEff a) : Pure pureEff (Tm.instantiate b a) := by
  apply bsubst (σ := Fin.cases a fun i => .bv i) ?_ hb
  intro i
  exact Fin.cases ha (fun _ => .bv) i

@[simp] theorem not_iter {n : Nat} (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) :
    ¬ Pure pureEff (.iter a b) := by intro h; cases h

end Pure
end Purity

section Examples

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Isotope.Ctx ν τ} {n : Nat} {β : BoundCtx τ n}

/-- Product elimination puts the right component at index zero. -/
example {a b : Tm ν Φ n} {A B : τ} (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B) :
    HasType Φ Γ β (.let₂ (.pair a b) (.pair (.bv 0) (.bv 1))) (Silmaril.product B A) :=
  .let₂ (.pair ha hb) (.pair .bv .bv)

/-- Each case branch receives its own summand's type. -/
example {e : Tm ν Φ n} {A B : τ} (he : HasType Φ Γ β e (Silmaril.coprod A B)) :
    HasType Φ Γ β (.case e (.inl (.bv 0)) (.inr (.bv 0))) (Silmaril.coprod A B) :=
  .case he (.inl .bv) (.inr .bv)

/-- An iteration body returns its result on the left and its next state on the right. -/
example (f : Φ) {a : Tm ν Φ n} (ha : HasType Φ Γ β a (instrSrc f)) :
    HasType Φ Γ β (.iter a (.inl (.op f (.bv 0)))) (instrTrg f) :=
  .iter ha (.inl (.op .bv))

end Examples

end Silmaril.Isotope.LetIter.LocallyNameless
