module

public import Silmaril.SSA.Isotope.Bridge.Defs

/-!
# Bridge between legacy and thesis let-iter: syntax and contexts (proofs)

Round trips of the term and context translations, and commutation of the term
translation with every syntactic operation used by the axiom schemes: renaming,
`lift`, `underBinder`, `underTwoBinders`, bound substitution, `instantiate` and
free substitution. Restated in `Silmaril.SSA.Isotope.Bridge.Thms`.
-/

@[expose] public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.Bridge

open Silmaril.Isotope.Bridge

local notation "LTm" => Silmaril.Isotope.LetIter.LocallyNameless.Tm
local notation "TTm" => Silmaril.Thesis.LambdaIter.LocallyNameless.Tm

variable {ν : Type w} {Φ : Type v}

/-! ## Round trips -/

@[simp] theorem ofThesis_toThesis {n : Nat} (t : LTm ν Φ n) : ofThesis (toThesis t) = t := by
  induction t with
  | fv x => rfl
  | bv i => rfl
  | op f a iha => simp only [toThesis, ofThesis, iha]
  | let₁ a b iha ihb => simp only [toThesis, ofThesis, iha, ihb]
  | unit => rfl
  | pair a b iha ihb => simp only [toThesis, ofThesis, iha, ihb]
  | let₂ a b iha ihb => simp only [toThesis, ofThesis, iha, ihb]
  | inl a iha => simp only [toThesis, ofThesis, iha]
  | inr a iha => simp only [toThesis, ofThesis, iha]
  | case e l r ihe ihl ihr => simp only [toThesis, ofThesis, ihe, ihl, ihr]
  | abort a iha => simp only [toThesis, ofThesis, iha]
  | iter a b iha ihb => simp only [toThesis, ofThesis, iha, ihb]

@[simp] theorem toThesis_ofThesis {n : Nat} (t : TTm ν Φ n) : toThesis (ofThesis t) = t := by
  induction t with
  | fv x => rfl
  | bv i => rfl
  | op f a iha => simp only [toThesis, ofThesis, iha]
  | let₁ a b iha ihb => simp only [toThesis, ofThesis, iha, ihb]
  | unit => rfl
  | pair a b iha ihb => simp only [toThesis, ofThesis, iha, ihb]
  | let₂ a b iha ihb => simp only [toThesis, ofThesis, iha, ihb]
  | inl a iha => simp only [toThesis, ofThesis, iha]
  | inr a iha => simp only [toThesis, ofThesis, iha]
  | case e l r ihe ihl ihr => simp only [toThesis, ofThesis, ihe, ihl, ihr]
  | abort a iha => simp only [toThesis, ofThesis, iha]
  | iter a b iha ihb => simp only [toThesis, ofThesis, iha, ihb]

theorem toThesis_injective {n : Nat} : Function.Injective (toThesis (ν := ν) (Φ := Φ) (n := n)) :=
  fun a b h => by rw [← ofThesis_toThesis a, h, ofThesis_toThesis]

theorem ofThesis_injective {n : Nat} : Function.Injective (ofThesis (ν := ν) (Φ := Φ) (n := n)) :=
  fun a b h => by rw [← toThesis_ofThesis a, h, toThesis_ofThesis]

/-- The term translation is an equivalence of types, for every scope `n`. -/
def tmEquiv (ν : Type w) (Φ : Type v) (n : Nat) : LTm ν Φ n ≃ TTm ν Φ n where
  toFun := toThesis
  invFun := ofThesis
  left_inv := ofThesis_toThesis
  right_inv := toThesis_ofThesis

/-! ## Commutation with syntactic operations -/

theorem toThesis_rename {n m : Nat} (ρ : Fin n → Fin m) (t : LTm ν Φ n) :
    toThesis (Silmaril.Isotope.LetIter.LocallyNameless.Tm.rename ρ t) =
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.rename ρ (toThesis t) := by
  induction t generalizing m with
  | fv x => rfl
  | bv i => rfl
  | op f a iha =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.rename,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.rename, toThesis, iha]
  | let₁ a b iha ihb =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.rename,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.rename, toThesis, iha, ihb]
      rfl
  | unit => rfl
  | pair a b iha ihb =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.rename,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.rename, toThesis, iha, ihb]
  | let₂ a b iha ihb =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.rename,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.rename, toThesis, iha, ihb]
      rfl
  | inl a iha =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.rename,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.rename, toThesis, iha]
  | inr a iha =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.rename,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.rename, toThesis, iha]
  | case e l r ihe ihl ihr =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.rename,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.rename, toThesis, ihe, ihl, ihr]
      rfl
  | abort a iha =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.rename,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.rename, toThesis, iha]
  | iter a b iha ihb =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.rename,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.rename, toThesis, iha, ihb]
      rfl

theorem toThesis_lift {n : Nat} (t : LTm ν Φ n) :
    toThesis (Silmaril.Isotope.LetIter.LocallyNameless.Tm.lift t) =
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.lift (toThesis t) :=
  toThesis_rename _ t

theorem toThesis_underBinder {n : Nat} (t : LTm ν Φ (n + 1)) :
    toThesis (Silmaril.Isotope.LetIter.LocallyNameless.Tm.underBinder t) =
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.underBinder (toThesis t) :=
  toThesis_rename _ t

theorem toThesis_underTwoBinders {n : Nat} (t : LTm ν Φ (n + 2)) :
    toThesis (Silmaril.Isotope.LetIter.LocallyNameless.Tm.underTwoBinders t) =
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.underTwoBinders (toThesis t) :=
  toThesis_rename _ t

theorem toThesis_upSub {n m : Nat} (σ : Fin n → LTm ν Φ m) :
    (fun i => toThesis (Silmaril.Isotope.LetIter.LocallyNameless.Tm.upSub σ i)) =
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.upSubAux (fun i => toThesis (σ i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Silmaril.Isotope.LetIter.LocallyNameless.Tm.upSub,
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.upSubAux, toThesis]
  · simp [Silmaril.Isotope.LetIter.LocallyNameless.Tm.upSub,
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.upSubAux, toThesis_lift]

theorem toThesis_bsubst {n m : Nat} (σ : Fin n → LTm ν Φ m) (t : LTm ν Φ n) :
    toThesis (Silmaril.Isotope.LetIter.LocallyNameless.Tm.bsubst σ t) =
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.bsubst (fun i => toThesis (σ i))
        (toThesis t) := by
  induction t generalizing m with
  | fv x => rfl
  | bv i => rfl
  | op f a iha =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.bsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.bsubst, toThesis, iha]
  | let₁ a b iha ihb =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.bsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.bsubst, toThesis, iha, ihb, toThesis_upSub]
  | unit => rfl
  | pair a b iha ihb =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.bsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.bsubst, toThesis, iha, ihb]
  | let₂ a b iha ihb =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.bsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.bsubst, toThesis, iha, ihb, toThesis_upSub]
  | inl a iha =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.bsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.bsubst, toThesis, iha]
  | inr a iha =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.bsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.bsubst, toThesis, iha]
  | case e l r ihe ihl ihr =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.bsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.bsubst, toThesis, ihe, ihl, ihr,
        toThesis_upSub]
  | abort a iha =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.bsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.bsubst, toThesis, iha]
  | iter a b iha ihb =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.bsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.bsubst, toThesis, iha, ihb, toThesis_upSub]

theorem toThesis_instantiate {n : Nat} (b : LTm ν Φ (n + 1)) (a : LTm ν Φ n) :
    toThesis (Silmaril.Isotope.LetIter.LocallyNameless.Tm.instantiate b a) =
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.instantiate (toThesis b) (toThesis a) := by
  simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.instantiate,
    Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.instantiate, toThesis_bsubst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [toThesis]

theorem toThesis_fsubst [DecidableEq ν] {n : Nat} (x : ν) (s : LTm ν Φ n) (t : LTm ν Φ n) :
    toThesis (Silmaril.Isotope.LetIter.LocallyNameless.Tm.fsubst x s t) =
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.fsubst x (toThesis s) (toThesis t) := by
  induction t with
  | fv y =>
      by_cases h : x = y
      · simp [Silmaril.Isotope.LetIter.LocallyNameless.Tm.fsubst, h, toThesis]
      · simp [Silmaril.Isotope.LetIter.LocallyNameless.Tm.fsubst, h, toThesis]
  | bv i => rfl
  | op f a iha =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.fsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.fsubst, toThesis, iha]
  | let₁ a b iha ihb =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.fsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.fsubst, toThesis, iha, ihb, toThesis_lift]
  | unit => rfl
  | pair a b iha ihb =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.fsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.fsubst, toThesis, iha, ihb]
  | let₂ a b iha ihb =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.fsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.fsubst, toThesis, iha, ihb, toThesis_lift]
  | inl a iha =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.fsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.fsubst, toThesis, iha]
  | inr a iha =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.fsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.fsubst, toThesis, iha]
  | case e l r ihe ihl ihr =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.fsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.fsubst, toThesis, ihe, ihl, ihr,
        toThesis_lift]
  | abort a iha =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.fsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.fsubst, toThesis, iha]
  | iter a b iha ihb =>
      simp only [Silmaril.Isotope.LetIter.LocallyNameless.Tm.fsubst,
        Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.fsubst, toThesis, iha, ihb, toThesis_lift]

/-! ### The reverse translation commutes too (via the round trips) -/

theorem ofThesis_lift {n : Nat} (t : TTm ν Φ n) :
    ofThesis (Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.lift t) =
      Silmaril.Isotope.LetIter.LocallyNameless.Tm.lift (ofThesis t) := by
  apply toThesis_injective
  rw [toThesis_ofThesis, toThesis_lift, toThesis_ofThesis]

theorem ofThesis_underBinder {n : Nat} (t : TTm ν Φ (n + 1)) :
    ofThesis (Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.underBinder t) =
      Silmaril.Isotope.LetIter.LocallyNameless.Tm.underBinder (ofThesis t) := by
  apply toThesis_injective
  rw [toThesis_ofThesis, toThesis_underBinder, toThesis_ofThesis]

theorem ofThesis_underTwoBinders {n : Nat} (t : TTm ν Φ (n + 2)) :
    ofThesis (Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.underTwoBinders t) =
      Silmaril.Isotope.LetIter.LocallyNameless.Tm.underTwoBinders (ofThesis t) := by
  apply toThesis_injective
  rw [toThesis_ofThesis, toThesis_underTwoBinders, toThesis_ofThesis]

theorem ofThesis_instantiate {n : Nat} (b : TTm ν Φ (n + 1)) (a : TTm ν Φ n) :
    ofThesis (Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.instantiate b a) =
      Silmaril.Isotope.LetIter.LocallyNameless.Tm.instantiate (ofThesis b) (ofThesis a) := by
  apply toThesis_injective
  rw [toThesis_ofThesis, toThesis_instantiate, toThesis_ofThesis, toThesis_ofThesis]

/-! ## Contexts -/

section Contexts

variable {τ : Type u}

@[simp] theorem Ctx.ofThesis_toThesis (Γ : Silmaril.Isotope.Ctx ν τ) :
    Ctx.ofThesis (Ctx.toThesis Γ) = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ x A ih => simp only [Ctx.toThesis, Ctx.ofThesis, ih]

@[simp] theorem Ctx.toThesis_ofThesis (Γ : Silmaril.Thesis.LambdaIter.Ctx ν τ) :
    Ctx.toThesis (Ctx.ofThesis Γ) = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ x A ih => simp only [Ctx.toThesis, Ctx.ofThesis, ih]

/-- Context translation as an equivalence of types. -/
def Ctx.equiv (ν : Type w) (τ : Type u) :
    Silmaril.Isotope.Ctx ν τ ≃ Silmaril.Thesis.LambdaIter.Ctx ν τ where
  toFun := Ctx.toThesis
  invFun := Ctx.ofThesis
  left_inv := Ctx.ofThesis_toThesis
  right_inv := Ctx.toThesis_ofThesis

@[simp] theorem Ctx.lookup_toThesis [DecidableEq ν] (Γ : Silmaril.Isotope.Ctx ν τ) (x : ν) :
    (Ctx.toThesis Γ).lookup x = Γ.lookup x := by
  induction Γ with
  | nil => rfl
  | snoc Γ y A ih =>
      cases y with
      | none => simpa only [Ctx.toThesis, Silmaril.Thesis.LambdaIter.Ctx.lookup,
          Silmaril.Isotope.Ctx.lookup] using ih
      | some y =>
          simp only [Ctx.toThesis, Silmaril.Thesis.LambdaIter.Ctx.lookup,
            Silmaril.Isotope.Ctx.lookup, ih]

@[simp] theorem Ctx.lookup_ofThesis [DecidableEq ν] (Γ : Silmaril.Thesis.LambdaIter.Ctx ν τ)
    (x : ν) : (Ctx.ofThesis Γ).lookup x = Γ.lookup x := by
  rw [← Ctx.lookup_toThesis, Ctx.toThesis_ofThesis]

@[simp] theorem BoundCtx.ofThesis_toThesis {n : Nat} (β : Silmaril.Isotope.BoundCtx τ n) :
    BoundCtx.ofThesis (BoundCtx.toThesis β) = β := by
  induction β with
  | nil => rfl
  | snoc β A ih => simp only [BoundCtx.toThesis, BoundCtx.ofThesis, ih]

@[simp] theorem BoundCtx.toThesis_ofThesis {n : Nat}
    (β : Silmaril.Thesis.LambdaIter.LocallyNameless.BoundCtx τ n) :
    BoundCtx.toThesis (BoundCtx.ofThesis β) = β := by
  induction β with
  | nil => rfl
  | snoc β A ih => simp only [BoundCtx.toThesis, BoundCtx.ofThesis, ih]

/-- Bound-context translation as an equivalence of types. -/
def BoundCtx.equiv (τ : Type u) (n : Nat) :
    Silmaril.Isotope.BoundCtx τ n ≃ Silmaril.Thesis.LambdaIter.LocallyNameless.BoundCtx τ n where
  toFun := BoundCtx.toThesis
  invFun := BoundCtx.ofThesis
  left_inv := BoundCtx.ofThesis_toThesis
  right_inv := BoundCtx.toThesis_ofThesis

@[simp] theorem BoundCtx.get_toThesis {n : Nat} (β : Silmaril.Isotope.BoundCtx τ n) :
    ∀ i : Fin n, (BoundCtx.toThesis β).get i = β.get i := by
  induction β with
  | nil => intro i; exact Fin.elim0 i
  | snoc β A ih =>
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih j

@[simp] theorem BoundCtx.get_ofThesis {n : Nat}
    (β : Silmaril.Thesis.LambdaIter.LocallyNameless.BoundCtx τ n) (i : Fin n) :
    (BoundCtx.ofThesis β).get i = β.get i := by
  rw [← BoundCtx.get_toThesis, BoundCtx.toThesis_ofThesis]

end Contexts

end Silmaril.Proofs.SSA.Isotope.Bridge
