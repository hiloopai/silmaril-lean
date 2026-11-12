module

public import Mathlib.Data.Fin.Basic

/-!
# Sequential terms with products and unit

Free names remain named; bound variables use finite de Bruijn indices. Raw
syntax needs no type operations, instruction signature, or effects.
-/

@[expose] public section

universe u v

variable {ν : Type u} {Φ : Type v} {n m k : Nat}

namespace Silmaril.Isotope.LetSeq.LocallyNameless

/-- Locally nameless terms with `n` in-scope bound variables. -/
inductive Tm (ν : Type u) (Φ : Type v) : Nat → Type (max u v) where
  | fv {n : Nat} (x : ν) : Tm ν Φ n
  | bv {n : Nat} (ι : Fin n) : Tm ν Φ n
  | op {n : Nat} (f : Φ) (a : Tm ν Φ n) : Tm ν Φ n
  | let₁ {n : Nat} (a : Tm ν Φ n) (b : Tm ν Φ (n + 1)) : Tm ν Φ n
  | unit {n : Nat} : Tm ν Φ n
  | pair {n : Nat} (a b : Tm ν Φ n) : Tm ν Φ n
  | let₂ {n : Nat} (a : Tm ν Φ n) (b : Tm ν Φ (n + 2)) : Tm ν Φ n
  deriving Repr, DecidableEq

namespace Tm

def up (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => Fin.succ (ρ i))

/-- Rename bound variables. -/
def rename {n m : Nat} (ρ : Fin n → Fin m) : Tm ν Φ n → Tm ν Φ m
  | .fv x => .fv x
  | .bv i => .bv (ρ i)
  | .op f a => .op f (rename ρ a)
  | .let₁ a b => .let₁ (rename ρ a) (rename (up ρ) b)
  | .unit => .unit
  | .pair a b => .pair (rename ρ a) (rename ρ b)
  | .let₂ a b => .let₂ (rename ρ a) (rename (up (up ρ)) b)

def lift (t : Tm ν Φ n) : Tm ν Φ (n + 1) := rename Fin.succ t

/-- Insert one ambient binder under the top binder, preserving index zero. -/
def underBinder (t : Tm ν Φ (n + 1)) : Tm ν Φ (n + 2) :=
  rename (Fin.cases 0 (fun i => Fin.succ (Fin.succ i))) t

/-- Inserting below the newest binder preserves index zero. -/
@[simp] theorem underBinder_bv_zero :
    underBinder (ν := ν) (Φ := Φ) (.bv (0 : Fin (n + 1))) =
      .bv (0 : Fin (n + 2)) := rfl

/-- Insert one ambient binder under the top two binders. -/
def underTwoBinders (t : Tm ν Φ (n + 2)) : Tm ν Φ (n + 3) :=
  rename (Fin.cases 0 (Fin.cases 1 (fun i => Fin.succ (Fin.succ (Fin.succ i))))) t

def upSub (σ : Fin n → Tm ν Φ m) : Fin (n + 1) → Tm ν Φ (m + 1) :=
  Fin.cases (.bv 0) (fun i => lift (σ i))

/-- Simultaneous, capture-avoiding substitution for bound variables. -/
def bsubst {n m : Nat} (σ : Fin n → Tm ν Φ m) : Tm ν Φ n → Tm ν Φ m
  | .fv x => .fv x
  | .bv i => σ i
  | .op f a => .op f (bsubst σ a)
  | .let₁ a b => .let₁ (bsubst σ a) (bsubst (upSub σ) b)
  | .unit => .unit
  | .pair a b => .pair (bsubst σ a) (bsubst σ b)
  | .let₂ a b => .let₂ (bsubst σ a) (bsubst (upSub (upSub σ)) b)

/-- Open the outermost binder. -/
def instantiate (b : Tm ν Φ (n + 1)) (a : Tm ν Φ n) : Tm ν Φ n :=
  bsubst (Fin.cases a (fun i => .bv i)) b

/-- Substitute a term for a free variable. -/
def fsubst {n : Nat} [DecidableEq ν] (x : ν) (s : Tm ν Φ n) : Tm ν Φ n → Tm ν Φ n
  | .fv y => if x = y then s else .fv y
  | .bv i => .bv i
  | .op f a => .op f (fsubst x s a)
  | .let₁ a b => .let₁ (fsubst x s a) (fsubst x (lift s) b)
  | .unit => .unit
  | .pair a b => .pair (fsubst x s a) (fsubst x s b)
  | .let₂ a b => .let₂ (fsubst x s a) (fsubst x (lift (lift s)) b)

@[simp] theorem fsubst_fv_self [DecidableEq ν] (x : ν) (s : Tm ν Φ n) :
    fsubst x s (.fv x) = s := by simp [fsubst]

@[simp] theorem fsubst_fv_ne [DecidableEq ν] {x y : ν} (h : x ≠ y) (s : Tm ν Φ n) :
    fsubst x s (.fv y) = .fv y := by simp [fsubst, h]

end Tm
end Silmaril.Isotope.LetSeq.LocallyNameless
