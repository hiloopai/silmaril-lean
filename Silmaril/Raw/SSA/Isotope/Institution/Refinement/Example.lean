module

public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.Isotope

@[expose] public section

/-!
# A concrete strict refinement theory

The general non-vacuity results of `Theories.lean` (`initialModel_holds_iff`, `entails_strict`)
show that a refinement theory entails exactly what its compatible preorder derives. This file
exhibits a concrete instance in which refinement is genuinely one-directional.

Take let-seq over simple types `Ty Unit` with no primitive instructions (`Instr` is empty), in
the context `ctxXY` with two free variables `x` (named `false`) and `y` (named `true`) of the base
type, and the single primitive rewrite `x ⊑ y` (`R`). Then in the let-seq refinement theory
`seqTheory false ctxXY R`:

* `x ⊑ y` is entailed (`entails_x_le_y`);
* `y ⊑ x` is not entailed (`not_entails_y_le_x`), because `y ⊑ x` is not derivable
  (`not_refinement_y_x`);
* hence the translated equation `x = y` is not entailed either (`not_entails_toRef`), so the
  theory is not the image of an equational theory.
-/

namespace Silmaril.Isotope.Institution.Refinement.Example

open CategoryTheory
open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Isotope.Theory
open Silmaril.Isotope.Institution.Refinement

/-- No primitive instructions. -/
inductive Instr : Type where

instance : HasTy Instr (Ty Unit) where
  src f := nomatch f
  trg f := nomatch f

instance : HasEff Instr Bool where
  eff f := nomatch f

/-- The base type. -/
abbrev base : Ty Unit := .base ()

/-- Two free variables of the base type: `x` is named `false`, `y` is named `true`. -/
abbrev ctxXY : Ctx Bool (Ty Unit) := (Ctx.nil.snoc (some false) base).snoc (some true) base

/-- Closed terms of the base type. -/
abbrev baseIndex : TypingIndex (Ty Unit) := ⟨0, .nil, base⟩

/-- The single primitive rewrite `x ⊑ y` at the base type. -/
def R : LetSeq.LocallyNameless.TypedRelation Bool Instr (Ty Unit) :=
  fun {_} _ a b A => a = .fv false ∧ b = .fv true ∧ A = base

/-- The free variable `x`, as exactly typed syntax. -/
def x : LetSeq.LocallyNameless.Models.Carrier Instr ctxXY baseIndex :=
  ⟨.fv false, .fv (by decide)⟩

/-- The free variable `y`, as exactly typed syntax. -/
def y : LetSeq.LocallyNameless.Models.Carrier Instr ctxXY baseIndex :=
  ⟨.fv true, .fv (by decide)⟩

/-! ### A monotone Boolean denotation

To show that `y ⊑ x` is not derivable we interpret terms as untyped values: the base type as
`Bool` (ordered `false ≤ true`), unit as a single value, and products as pairs ordered
componentwise. The free variables `x` and `y` denote `false` and `true`. Every equation is sound
for well-typed environments, every term is monotone in its environment, and the primitive rewrite
`x ⊑ y` holds, so every derivable refinement is valid; `y ⊑ x` would give `true ≤ false`. -/

/-- There are no instructions. -/
def instrElim {α : Sort _} (f : Instr) : α := nomatch f

/-- Untyped values: Booleans at the base type, unit, and pairs. -/
inductive Val : Type where
  | bit (b : Bool)
  | unit
  | pair (v w : Val)

namespace Val

/-- Componentwise order with `false ≤ true` at the base type. -/
inductive Le : Val → Val → Prop where
  | bit {b c : Bool} : b ≤ c → Le (.bit b) (.bit c)
  | unit : Le .unit .unit
  | pair {v v' w w' : Val} : Le v v' → Le w w' → Le (.pair v w) (.pair v' w')

theorem Le.refl : (v : Val) → Le v v
  | .bit _ => .bit le_rfl
  | .unit => .unit
  | .pair v w => .pair (Le.refl v) (Le.refl w)

theorem Le.trans {u v w : Val} (h : Le u v) (k : Le v w) : Le u w := by
  induction h generalizing w with
  | bit h => cases k with | bit k => exact .bit (h.trans k)
  | unit => exact k
  | pair _ _ ih1 ih2 => cases k with | pair k1 k2 => exact .pair (ih1 k1) (ih2 k2)

/-- First projection, total on all values. -/
def fst : Val → Val
  | .pair v _ => v
  | .bit b => .bit b
  | .unit => .unit

/-- Second projection, total on all values. -/
def snd : Val → Val
  | .pair _ w => w
  | .bit b => .bit b
  | .unit => .unit

theorem Le.fst {v w : Val} (h : Le v w) : Le v.fst w.fst := by
  cases h with
  | bit h => exact .bit h
  | unit => exact .unit
  | pair h _ => exact h

theorem Le.snd {v w : Val} (h : Le v w) : Le v.snd w.snd := by
  cases h with
  | bit h => exact .bit h
  | unit => exact .unit
  | pair _ h => exact h

/-- Values of each simple type. -/
def Typed : Val → Ty Unit → Prop
  | .bit _, .base _ => True
  | .unit, .unit => True
  | .pair v w, .product A B => Typed v A ∧ Typed w B
  | _, _ => False

theorem typed_unit {v : Val} (h : Typed v Ty.unit) : v = .unit := by
  cases v <;> simp_all [Typed]

theorem typed_product {v : Val} {A B : Ty Unit} (h : Typed v (Ty.product A B)) :
    ∃ p q, v = .pair p q ∧ Typed p A ∧ Typed q B := by
  cases v with
  | pair p q => exact ⟨p, q, rfl, h⟩
  | bit => simp [Typed] at h
  | unit => simp [Typed] at h

theorem typed_fst_snd {v : Val} {A B : Ty Unit} (h : Typed v (Ty.product A B)) :
    Typed v.fst A ∧ Typed v.snd B := by
  obtain ⟨p, q, rfl, hp, hq⟩ := typed_product h
  exact ⟨hp, hq⟩

end Val

/-- Environments for the bound variables. -/
abbrev Env (n : Nat) := Fin n → Val

/-- Extend an environment by a new newest bound variable. -/
def ext {n : Nat} (v : Val) (ρ : Env n) : Env (n + 1) := fun i => Fin.cases v ρ i

@[simp] theorem ext_zero {n : Nat} (v : Val) (ρ : Env n) : ext v ρ 0 = v := rfl

@[simp] theorem ext_succ {n : Nat} (v : Val) (ρ : Env n) (i : Fin n) :
    ext v ρ i.succ = ρ i := rfl

/-- The untyped denotation; `x` (named `false`) is `false` and `y` (named `true`) is `true`. -/
def den : {n : Nat} → LetSeq.LocallyNameless.Tm Bool Instr n → Env n → Val
  | _, .fv x, _ => .bit x
  | _, .bv i, ρ => ρ i
  | _, .op f _, _ => nomatch f
  | _, .let₁ a b, ρ => den b (ext (den a ρ) ρ)
  | _, .unit, _ => .unit
  | _, .pair a b, ρ => .pair (den a ρ) (den b ρ)
  | _, .let₂ a c, ρ => den c (ext (den a ρ).snd (ext (den a ρ).fst ρ))

theorem den_rename {n : Nat} (t : LetSeq.LocallyNameless.Tm Bool Instr n) :
    ∀ {m : Nat} (r : Fin n → Fin m) (ρ : Env m),
      den (LetSeq.LocallyNameless.Tm.rename r t) ρ = den t (ρ ∘ r) := by
  induction t with
  | fv => intros; rfl
  | bv => intros; rfl
  | op f => exact instrElim f
  | let₁ a b iha ihb =>
      intro m r ρ
      simp only [LetSeq.LocallyNameless.Tm.rename, den, iha, ihb]
      congr 1
      funext i
      cases i using Fin.cases <;> simp [LetSeq.LocallyNameless.Tm.up]
  | unit => intros; rfl
  | pair a b iha ihb =>
      intro m r ρ
      simp only [LetSeq.LocallyNameless.Tm.rename, den, iha, ihb]
  | let₂ a c iha ihc =>
      intro m r ρ
      simp only [LetSeq.LocallyNameless.Tm.rename, den, iha, ihc]
      congr 1
      funext i
      cases i using Fin.cases with
      | zero => simp [LetSeq.LocallyNameless.Tm.up]
      | succ j =>
          cases j using Fin.cases with
          | zero => rfl
          | succ k => simp [LetSeq.LocallyNameless.Tm.up]

theorem den_lift {n : Nat} (t : LetSeq.LocallyNameless.Tm Bool Instr n) (v : Val) (ρ : Env n) :
    den (LetSeq.LocallyNameless.Tm.lift t) (ext v ρ) = den t ρ := by
  simp only [LetSeq.LocallyNameless.Tm.lift, den_rename]
  rfl

theorem den_underBinder {n : Nat} (t : LetSeq.LocallyNameless.Tm Bool Instr (n + 1))
    (v w : Val) (ρ : Env n) :
    den (LetSeq.LocallyNameless.Tm.underBinder t) (ext v (ext w ρ)) = den t (ext v ρ) := by
  simp only [LetSeq.LocallyNameless.Tm.underBinder, den_rename]
  congr 1
  funext i
  cases i using Fin.cases <;> simp

theorem den_underTwoBinders {n : Nat} (t : LetSeq.LocallyNameless.Tm Bool Instr (n + 2))
    (u v w : Val) (ρ : Env n) :
    den (LetSeq.LocallyNameless.Tm.underTwoBinders t) (ext u (ext v (ext w ρ))) =
      den t (ext u (ext v ρ)) := by
  simp only [LetSeq.LocallyNameless.Tm.underTwoBinders, den_rename]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ j =>
      cases j using Fin.cases with
      | zero => rfl
      | succ k => simp

theorem den_bsubst {n : Nat} (t : LetSeq.LocallyNameless.Tm Bool Instr n) :
    ∀ {m : Nat} (σ : Fin n → LetSeq.LocallyNameless.Tm Bool Instr m) (ρ : Env m),
      den (LetSeq.LocallyNameless.Tm.bsubst σ t) ρ = den t (fun i => den (σ i) ρ) := by
  induction t with
  | fv => intros; rfl
  | bv => intros; rfl
  | op f => exact instrElim f
  | let₁ a b iha ihb =>
      intro m σ ρ
      simp only [LetSeq.LocallyNameless.Tm.bsubst, den, iha, ihb]
      congr 1
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ j => simp [LetSeq.LocallyNameless.Tm.upSub, den_lift]
  | unit => intros; rfl
  | pair a b iha ihb =>
      intro m σ ρ
      simp only [LetSeq.LocallyNameless.Tm.bsubst, den, iha, ihb]
  | let₂ a c iha ihc =>
      intro m σ ρ
      simp only [LetSeq.LocallyNameless.Tm.bsubst, den, iha, ihc]
      congr 1
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ j =>
          cases j using Fin.cases with
          | zero => rfl
          | succ k => simp [LetSeq.LocallyNameless.Tm.upSub, den_lift]

/-- Pointwise order of environments. -/
def EnvLe {n : Nat} (ρ₁ ρ₂ : Env n) : Prop := ∀ i, Val.Le (ρ₁ i) (ρ₂ i)

theorem EnvLe.refl {n : Nat} (ρ : Env n) : EnvLe ρ ρ := fun _ => .refl _

theorem EnvLe.ext {n : Nat} {v w : Val} {ρ₁ ρ₂ : Env n} (h : Val.Le v w)
    (hρ : EnvLe ρ₁ ρ₂) : EnvLe (ext v ρ₁) (ext w ρ₂) := by
  intro i
  cases i using Fin.cases with
  | zero => exact h
  | succ j => exact hρ j

/-- Every term denotes a monotone function of its environment. -/
theorem den_mono {n : Nat} (t : LetSeq.LocallyNameless.Tm Bool Instr n) :
    ∀ {ρ₁ ρ₂ : Env n}, EnvLe ρ₁ ρ₂ → Val.Le (den t ρ₁) (den t ρ₂) := by
  induction t with
  | fv => intros; exact .refl _
  | bv i => intro _ _ h; exact h i
  | op f => exact instrElim f
  | let₁ a b iha ihb => intro _ _ h; exact ihb (EnvLe.ext (iha h) h)
  | unit => intros; exact .unit
  | pair a b iha ihb => intro _ _ h; exact .pair (iha h) (ihb h)
  | let₂ a c iha ihc =>
      intro _ _ h
      exact ihc (EnvLe.ext (iha h).snd (EnvLe.ext (iha h).fst h))

/-- Environments whose values have the types of a bound context. -/
def TypedEnv {n : Nat} (β : BoundCtx (Ty Unit) n) (ρ : Env n) : Prop :=
  ∀ i, Val.Typed (ρ i) (β.get i)

theorem TypedEnv.ext {n : Nat} {β : BoundCtx (Ty Unit) n} {ρ : Env n} {v : Val} {A : Ty Unit}
    (hρ : TypedEnv β ρ) (hv : Val.Typed v A) : TypedEnv (.snoc β A) (ext v ρ) := by
  intro i
  cases i using Fin.cases with
  | zero => exact hv
  | succ j => exact hρ j

/-- Well-typed terms denote values of their type. -/
theorem den_typed {n : Nat} {β : BoundCtx (Ty Unit) n}
    {t : LetSeq.LocallyNameless.Tm Bool Instr n} {A : Ty Unit}
    (h : LetSeq.LocallyNameless.HasType Instr ctxXY β t A) :
    ∀ ρ, TypedEnv β ρ → Val.Typed (den t ρ) A := by
  induction h with
  | @fv _ _ x _ hx =>
      intro _ _
      cases x <;> simp [Ctx.lookup] at hx <;> subst hx <;> exact trivial
  | bv => intro _ hρ; exact hρ _
  | op => exact instrElim ‹Instr›
  | let₁ _ _ iha ihb => intro ρ hρ; exact ihb _ (hρ.ext (iha ρ hρ))
  | unit => intros; exact trivial
  | pair _ _ iha ihb => intro ρ hρ; exact ⟨iha ρ hρ, ihb ρ hρ⟩
  | let₂ _ _ iha ihb =>
      intro ρ hρ
      have h := Val.typed_fst_snd (iha ρ hρ)
      exact ihb _ ((hρ.ext h.1).ext h.2)

/-- Each well-typed instance of an axiom scheme is sound in well-typed environments. -/
theorem den_ax {n : Nat} {β : BoundCtx (Ty Unit) n}
    {a b : LetSeq.LocallyNameless.Tm Bool Instr n} {A : Ty Unit}
    (hax : LetSeq.LocallyNameless.CoreAxiom false a b)
    (ha : LetSeq.LocallyNameless.HasType Instr ctxXY β a A)
    (hb : LetSeq.LocallyNameless.HasType Instr ctxXY β b A) (ρ : Env n) (hρ : TypedEnv β ρ) :
    den a ρ = den b ρ := by
  cases hax with
  | structural h =>
      cases h with
      | letBeta _ =>
          simp only [den, LetSeq.LocallyNameless.Tm.instantiate, den_bsubst]
          congr 1
          funext i
          cases i using Fin.cases <;> rfl
      | letEta => rfl
      | unitEta a =>
          cases ha with
          | let₁ _ hu =>
              cases hu
              exact (Val.typed_unit (den_typed hb ρ hρ)).symm
      | pairBeta a b c =>
          simp only [den, den_lift, Val.fst, Val.snd]
      | pairEta a =>
          cases ha with
          | let₂ ha' _ =>
              obtain ⟨p, q, hpq, _, _⟩ := Val.typed_product (den_typed ha' ρ hρ)
              simp only [den, hpq, Val.fst, Val.snd]
              rfl
  | sequencing h =>
      cases h with
      | bindOp => exact instrElim ‹Instr›
      | bindLet a b c => simp only [den, den_underBinder]
      | bindLetPair e c d => simp only [den, den_underBinder]
      | bindPair a c => simp only [den, ext_zero, den_underTwoBinders]

/-- The typed equational theory is sound in well-typed environments. -/
theorem den_equiv {n : Nat} {β : BoundCtx (Ty Unit) n}
    {a b : LetSeq.LocallyNameless.Tm Bool Instr n} {A : Ty Unit}
    (h : LetSeq.LocallyNameless.Equiv false ctxXY β a b A) :
    ∀ ρ, TypedEnv β ρ → den a ρ = den b ρ := by
  induction h with
  | refl => intros; rfl
  | symm _ ih => intro ρ hρ; exact (ih ρ hρ).symm
  | trans _ _ ih ik => intro ρ hρ; exact (ih ρ hρ).trans (ik ρ hρ)
  | op => exact instrElim ‹Instr›
  | let₁ ha _ iha ihb =>
      intro ρ hρ
      simp only [den]
      rw [iha ρ hρ]
      exact ihb _ (hρ.ext (den_typed ha.hasType.2 ρ hρ))
  | unit => intros; rfl
  | pair _ _ iha ihb =>
      intro ρ hρ
      simp only [den, iha ρ hρ, ihb ρ hρ]
  | let₂ he _ ihe ihc =>
      intro ρ hρ
      simp only [den]
      rw [ihe ρ hρ]
      have h := Val.typed_fst_snd (den_typed he.hasType.2 ρ hρ)
      exact ihc _ ((hρ.ext h.1).ext h.2)
  | ax hax ha hb => intro ρ hρ; exact den_ax hax ha hb ρ hρ

/-- Every derivable refinement is valid in the Boolean denotation. -/
theorem den_refinement {n : Nat} {β : BoundCtx (Ty Unit) n}
    {a b : LetSeq.LocallyNameless.Tm Bool Instr n} {A : Ty Unit}
    (h : LetSeq.LocallyNameless.Refinement false ctxXY R β a b A) :
    ∀ ρ, TypedEnv β ρ → Val.Le (den a ρ) (den b ρ) := by
  induction h with
  | equiv h => intro ρ hρ; rw [den_equiv h ρ hρ]; exact .refl _
  | primitive h _ _ =>
      obtain ⟨rfl, rfl, rfl⟩ := h
      intros
      exact .bit (by decide)
  | trans _ _ ih ik => intro ρ hρ; exact (ih ρ hρ).trans (ik ρ hρ)
  | op => exact instrElim ‹Instr›
  | let₁ h0 _ ih0 ih1 =>
      intro ρ hρ
      exact (den_mono _ (EnvLe.ext (ih0 ρ hρ) (EnvLe.refl ρ))).trans
        (ih1 _ (hρ.ext (den_typed h0.hasType.2 ρ hρ)))
  | pair _ _ ih0 ih1 => intro ρ hρ; exact .pair (ih0 ρ hρ) (ih1 ρ hρ)
  | let₂ h0 _ ih0 ih1 =>
      intro ρ hρ
      have h := Val.typed_fst_snd (den_typed h0.hasType.2 ρ hρ)
      exact (den_mono _
          (EnvLe.ext (ih0 ρ hρ).snd (EnvLe.ext (ih0 ρ hρ).fst (EnvLe.refl ρ)))).trans
        (ih1 _ ((hρ.ext h.1).ext h.2))

/-- `x ⊑ y` is derivable: it is the primitive rewrite. -/
theorem refinement_x_y :
    LetSeq.LocallyNameless.Refinement false ctxXY R .nil (.fv false) (.fv true) base :=
  .primitive ⟨rfl, rfl, rfl⟩ (.fv (by decide)) (.fv (by decide))

/-- `y ⊑ x` is not derivable: it would be valid in the Boolean denotation, giving
`true ≤ false`. -/
theorem not_refinement_y_x :
    ¬ LetSeq.LocallyNameless.Refinement false ctxXY R .nil (.fv true) (.fv false) base := by
  intro h
  have hle : Val.Le (.bit true) (.bit false) :=
    den_refinement h (Fin.elim0 : Env 0) (fun i => i.elim0)
  cases hle with
  | bit h' => exact absurd h' (by decide)

/-- The let-seq refinement theory of `R` entails `x ⊑ y`. From `seq_entails_iff`. -/
theorem entails_x_le_y :
    (institution.obj (seqPSig Instr ctxXY)).Entails (seqTheory false ctxXY R).sentences
      ([⟨baseIndex, x, y⟩] : Sentence (seqPSig Instr ctxXY)) :=
  (seq_entails_iff false ctxXY R x y).2 refinement_x_y

/-- The let-seq refinement theory of `R` does not entail `y ⊑ x`. From `seq_entails_iff`. -/
theorem not_entails_y_le_x :
    ¬ (institution.obj (seqPSig Instr ctxXY)).Entails (seqTheory false ctxXY R).sentences
      ([⟨baseIndex, y, x⟩] : Sentence (seqPSig Instr ctxXY)) :=
  fun h => not_refinement_y_x ((seq_entails_iff false ctxXY R y x).1 h)

/-- The let-seq refinement theory of `R` does not entail the translated equation `x = y`. From
`seq_entails_toRef_iff`. -/
theorem not_entails_toRef :
    ¬ (institution.obj (seqPSig Instr ctxXY)).Entails (seqTheory false ctxXY R).sentences
      (Pair.toRef (⟨baseIndex, x, y⟩ : Pair (seqPSig Instr ctxXY))) :=
  fun h => not_refinement_y_x ((seq_entails_toRef_iff false ctxXY R x y).1 h).2

end Silmaril.Isotope.Institution.Refinement.Example
