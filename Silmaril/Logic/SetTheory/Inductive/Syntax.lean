module

public import Mathlib.Data.Fin.Basic

@[expose] public section

/-!
# Scoped syntax for the pure membership language

There are no function symbols: a term is a variable in `Fin n`. Quantifiers
extend the context at its head; index zero denotes the bound variable. A
sentence has context size zero. None of these definitions uses semantic
predicates or classical inference rules.
-/

namespace Silmaril.Logic.SetTheory.Inductive

/-- Terms in a context of exactly `n` available variables. -/
abbrev Term (n : Nat) := Fin n

/-- Finite first-order membership formulas, scoped by their variable context. -/
inductive Formula : Nat → Type
  | bot {n} : Formula n
  | eq {n} (x y : Term n) : Formula n
  | mem {n} (x y : Term n) : Formula n
  | neg {n} (p : Formula n) : Formula n
  | imp {n} (p q : Formula n) : Formula n
  | iff {n} (p q : Formula n) : Formula n
  | conj {n} (p q : Formula n) : Formula n
  | disj {n} (p q : Formula n) : Formula n
  | all {n} (p : Formula (n + 1)) : Formula n
  | ex {n} (p : Formula (n + 1)) : Formula n
  deriving DecidableEq, Repr

/-- Closed formulas. -/
abbrev Sentence := Formula 0

namespace Formula

/-- Lift a variable substitution through one binder without capture. -/
def lift {n m : Nat} (σ : Term n → Term m) : Term (n + 1) → Term (m + 1) :=
  Fin.cases 0 (fun i => (σ i).succ)

@[simp] theorem lift_zero {n m : Nat} (σ : Term n → Term m) : lift σ 0 = 0 := rfl
@[simp] theorem lift_succ {n m : Nat} (σ : Term n → Term m) (i : Term n) :
    lift σ i.succ = (σ i).succ := rfl

/-- Simultaneous capture-avoiding substitution. In this function-free
language every substitution term is itself a variable. -/
def subst {n m : Nat} (σ : Term n → Term m) : Formula n → Formula m
  | .bot => .bot
  | .eq x y => .eq (σ x) (σ y)
  | .mem x y => .mem (σ x) (σ y)
  | .neg p => .neg (subst σ p)
  | .imp p q => .imp (subst σ p) (subst σ q)
  | .iff p q => .iff (subst σ p) (subst σ q)
  | .conj p q => .conj (subst σ p) (subst σ q)
  | .disj p q => .disj (subst σ p) (subst σ q)
  | .all p => .all (subst (lift σ) p)
  | .ex p => .ex (subst (lift σ) p)

/-- Add a fresh variable at the head of the context. -/
def weaken {n : Nat} (p : Formula n) : Formula (n + 1) := p.subst Fin.succ

/-- Substitute a term for the outermost bound variable. -/
def instantiate {n : Nat} (p : Formula (n + 1)) (t : Term n) : Formula n :=
  p.subst (Fin.cases t id)

@[simp] theorem lift_id (n : Nat) : lift (id : Term n → Term n) = id := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem subst_id {n : Nat} (p : Formula n) : p.subst id = p := by
  induction p <;> simp [subst, *]

@[simp] theorem lift_comp {n m k : Nat} (σ : Term n → Term m) (τ : Term m → Term k) :
    lift (τ ∘ σ) = lift τ ∘ lift σ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Substitution composes, including underneath quantifiers. -/
theorem subst_subst {n m k : Nat} (p : Formula n) (σ : Term n → Term m)
    (τ : Term m → Term k) : (p.subst σ).subst τ = p.subst (τ ∘ σ) := by
  induction p generalizing m k <;> simp [subst, *, lift_comp]

@[simp] theorem instantiate_weaken {n : Nat} (p : Formula n) (t : Term n) :
    p.weaken.instantiate t = p := by
  simp only [instantiate, weaken, subst_subst]
  exact subst_id p

end Formula
end Silmaril.Logic.SetTheory.Inductive
