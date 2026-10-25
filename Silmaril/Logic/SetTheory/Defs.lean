module

public import Silmaril.Logic.SetTheory.Inductive.ZFC

/-! The scoped membership language and its ZF/ZFC proof systems. Formulas use
finite variable indices; substitution shifts binders to avoid capture. The
ZF axioms are independent finite formulas matching the nine primitive
set-theoretic schemas of set.mm's ZF0. ZFC extends that proof system by the
displayed choice schema. The semantic models are membership structures, with
Mathlib's `ZFSet` furnishing a model in Lean. -/
