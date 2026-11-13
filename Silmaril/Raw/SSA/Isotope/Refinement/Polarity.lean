module

public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace Silmaril.Isotope.Refinement

/-- The two directions of an inequation, without assuming symmetry. -/
inductive Polarity where
  | positive
  | negative
  deriving DecidableEq, Repr

namespace Polarity

def reverse : Polarity → Polarity
  | .positive => .negative
  | .negative => .positive

@[simp] theorem reverse_reverse (p : Polarity) : p.reverse.reverse = p := by cases p <;> rfl

universe u v w

/-- Negative polarity exchanges endpoints, also for proof-relevant relations. -/
def orient {α : Sort u} (p : Polarity) (R : α → α → Sort v) (a b : α) : Sort v :=
  match p with
  | .positive => R a b
  | .negative => R b a

@[simp] theorem orient_positive {α : Sort u} (R : α → α → Sort v) (a b : α) :
    orient positive R a b = R a b := rfl

@[simp] theorem orient_negative {α : Sort u} (R : α → α → Sort v) (a b : α) :
    orient negative R a b = R b a := rfl

@[simp] theorem orient_reverse {α : Sort u} (p : Polarity) (R : α → α → Sort v) (a b : α) :
    orient p.reverse R a b = orient p R b a := by cases p <;> rfl

/-- A relation-preserving map preserves each direction of a judgment. -/
def orientMap {α : Sort u} {β : Sort w} (p : Polarity) {R : α → α → Sort v}
    {Q : β → β → Sort v} (f : α → β) (h : ∀ {a b}, R a b → Q (f a) (f b))
    {a b : α} : p.orient R a b → p.orient Q (f a) (f b) := by
  cases p <;> exact h

instance : Fintype Polarity where
  elems := {.positive, .negative}
  complete := by intro p; cases p <;> simp

end Polarity
end Silmaril.Isotope.Refinement
