module

public import Mathlib.Data.Fin.Basic

@[expose] public section

/-! Independently defined, intrinsically scoped first-order arithmetic syntax.
Index zero is the newest variable. Substitution lifts under binders, preventing capture. -/
namespace Silmaril.Logic.Arithmetic

variable {n m : ℕ}

inductive Term (n : ℕ) where
  | var : Fin n → Term n
  | zero : Term n
  | succ : Term n → Term n
  | add : Term n → Term n → Term n
  | mul : Term n → Term n → Term n
  deriving DecidableEq, Repr

namespace Term

def rename {n m : ℕ} (ρ : Fin n → Fin m) : Term n → Term m
  | .var i => .var (ρ i)
  | .zero => .zero
  | .succ t => .succ (rename ρ t)
  | .add s t => .add (rename ρ s) (rename ρ t)
  | .mul s t => .mul (rename ρ s) (rename ρ t)

def subst {n m : ℕ} (σ : Fin n → Term m) : Term n → Term m
  | .var i => σ i
  | .zero => .zero
  | .succ t => .succ (subst σ t)
  | .add s t => .add (subst σ s) (subst σ t)
  | .mul s t => .mul (subst σ s) (subst σ t)

abbrev shift (t : Term n) : Term (n + 1) := t.rename Fin.succ

def liftSubst (σ : Fin n → Term m) : Fin (n + 1) → Term (m + 1) :=
  Fin.cases (.var 0) (fun i => (σ i).shift)

abbrev numeral : ℕ → Term n
  | 0 => .zero
  | k + 1 => .succ (numeral k)

end Term

inductive Formula : ℕ → Type where
  | bot {n : ℕ} : Formula n
  | equal {n : ℕ} : Term n → Term n → Formula n
  | imp {n : ℕ} : Formula n → Formula n → Formula n
  | conj {n : ℕ} : Formula n → Formula n → Formula n
  | disj {n : ℕ} : Formula n → Formula n → Formula n
  | all {n : ℕ} : Formula (n + 1) → Formula n
  | ex {n : ℕ} : Formula (n + 1) → Formula n
  deriving DecidableEq, Repr

namespace Formula

abbrev neg (φ : Formula n) := φ.imp .bot

def liftRename (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

def rename {n m : ℕ} (ρ : Fin n → Fin m) : Formula n → Formula m
  | .bot => .bot
  | .equal s t => .equal (s.rename ρ) (t.rename ρ)
  | .imp φ ψ => .imp (rename ρ φ) (rename ρ ψ)
  | .conj φ ψ => .conj (rename ρ φ) (rename ρ ψ)
  | .disj φ ψ => .disj (rename ρ φ) (rename ρ ψ)
  | .all φ => .all (rename (liftRename ρ) φ)
  | .ex φ => .ex (rename (liftRename ρ) φ)

def subst {n m : ℕ} (σ : Fin n → Term m) : Formula n → Formula m
  | .bot => .bot
  | .equal s t => .equal (s.subst σ) (t.subst σ)
  | .imp φ ψ => .imp (subst σ φ) (subst σ ψ)
  | .conj φ ψ => .conj (subst σ φ) (subst σ ψ)
  | .disj φ ψ => .disj (subst σ φ) (subst σ ψ)
  | .all φ => .all (subst (Term.liftSubst σ) φ)
  | .ex φ => .ex (subst (Term.liftSubst σ) φ)

abbrev shift (φ : Formula n) : Formula (n + 1) := φ.rename Fin.succ

/-- Substitute a term for the newest variable, retaining all parameters. -/
abbrev inst (φ : Formula (n + 1)) (t : Term n) : Formula n :=
  φ.subst (Fin.cases t Term.var)

/-- Induction step: replace the newest variable by its successor in the same scope. -/
def step (φ : Formula (n + 1)) : Formula (n + 1) :=
  φ.subst (Fin.cases (.succ (.var 0)) (fun i => .var i.succ))

end Formula

abbrev Sentence := Formula 0
abbrev Context (n : ℕ) := List (Formula n)

end Silmaril.Logic.Arithmetic
