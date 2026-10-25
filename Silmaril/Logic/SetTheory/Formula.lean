module

public import Mathlib.Logic.Function.Basic

@[expose] public section

/-!
# Semantic formulas over a membership structure

A structure for the language of set theory is a type `M` with a membership
relation. A valuation assigns an element of `M` to each set variable of a type
`V`. A semantic formula is a predicate on valuations. This is the shape in which
Metamath's metavariables are interpreted in a Carneiro-style model: a set
variable denotes a variable of `V`, and a wff metavariable denotes an arbitrary
predicate on valuations.

The connectives below are exactly those of set.mm, quantifiers update the
valuation, and a disjoint-variable condition `$d x ph` between a set variable
and a wff metavariable becomes `NotFree x φ`: the predicate ignores the value of
`x`.
-/

namespace Silmaril.Logic.SetTheory

universe u v

/-- A valuation of the set variables `V` in the structure `M`. -/
abbrev Env (M : Type u) (V : Type v) := V → M

/-- A semantic formula: a predicate on valuations. -/
abbrev Wff (M : Type u) (V : Type v) := Env M V → Prop

namespace Wff

variable {M : Type u} {V : Type v}

open Function

/-- Implication `( ph -> ps )`. -/
def imp (φ ψ : Wff M V) : Wff M V := fun ρ => φ ρ → ψ ρ

/-- Negation `-. ph`. -/
def not (φ : Wff M V) : Wff M V := fun ρ => ¬ φ ρ

/-- Conjunction `( ph /\ ps )`. -/
def and (φ ψ : Wff M V) : Wff M V := fun ρ => φ ρ ∧ ψ ρ

/-- Disjunction `( ph \/ ps )`. -/
def or (φ ψ : Wff M V) : Wff M V := fun ρ => φ ρ ∨ ψ ρ

/-- Biconditional `( ph <-> ps )`. -/
def iff (φ ψ : Wff M V) : Wff M V := fun ρ => φ ρ ↔ ψ ρ

/-- Equality of set variables `x = y`. -/
def eq (x y : V) : Wff M V := fun ρ => ρ x = ρ y

/-- Membership of set variables `x e. y`. -/
def mem [Membership M M] (x y : V) : Wff M V := fun ρ => ρ x ∈ ρ y

/-- The subclass relation `x C_ y` between set variables, interpreted by `df-ss`. -/
def ss [Membership M M] (x y : V) : Wff M V := fun ρ => ∀ a, a ∈ ρ x → a ∈ ρ y

/-- An arbitrary binary relation applied to two set variables. -/
def rel (R : M → M → Prop) (x y : V) : Wff M V := fun ρ => R (ρ x) (ρ y)

variable [DecidableEq V]

/-- Universal quantification `A. x ph`. -/
def all (x : V) (φ : Wff M V) : Wff M V := fun ρ => ∀ a, φ (update ρ x a)

/-- Existential quantification `E. x ph`. -/
def ex (x : V) (φ : Wff M V) : Wff M V := fun ρ => ∃ a, φ (update ρ x a)

/-- Explicit substitution `[ y / x ] ph`: evaluate `ph` with `x` set to the value of `y`. -/
def sb (y x : V) (φ : Wff M V) : Wff M V := fun ρ => φ (update ρ x (ρ y))

/-- Restricted universal quantification `A. x e. y ph` (`df-ral`). -/
def ral [Membership M M] (x y : V) (φ : Wff M V) : Wff M V := all x (imp (mem x y) φ)

/-- Restricted existential quantification `E. x e. y ph` (`df-rex`). -/
def rex [Membership M M] (x y : V) (φ : Wff M V) : Wff M V := ex x (and (mem x y) φ)

/-- The formula ignores the value of `x`. This interprets `$d x ph`. -/
def NotFree (x : V) (φ : Wff M V) : Prop := ∀ ρ a, φ (update ρ x a) ↔ φ ρ

end Wff

/-- A formula is valid if it holds under every valuation. -/
def Valid {M : Type u} {V : Type v} (φ : Wff M V) : Prop := ∀ ρ, φ ρ

namespace Wff

variable {M : Type u} {V : Type v} [DecidableEq V]

open Function

theorem NotFree.apply {x : V} {φ : Wff M V} (h : NotFree x φ) (ρ : Env M V) (a : M) :
    φ (update ρ x a) ↔ φ ρ :=
  h ρ a

/-- A formula not depending on `x` is unaffected by any change of `x`. -/
theorem NotFree.congr {x : V} {φ : Wff M V} (h : NotFree x φ) (ρ : Env M V) (a b : M) :
    φ (update ρ x a) ↔ φ (update ρ x b) := by
  rw [h, h]

/-- `A. x ph` does not depend on `x`. -/
theorem notFree_all (x : V) (φ : Wff M V) : NotFree x (all x φ) := by
  intro ρ a
  simp [all]

/-- `E. x ph` does not depend on `x`. -/
theorem notFree_ex (x : V) (φ : Wff M V) : NotFree x (ex x φ) := by
  intro ρ a
  simp [ex]

end Wff

end Silmaril.Logic.SetTheory
