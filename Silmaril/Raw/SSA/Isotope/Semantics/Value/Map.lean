module

public import Silmaril.SSA.Isotope.LambdaSSA.Defs
public import Mathlib.Logic.Equiv.Defs

/-! # Changing the atomic carrier of runtime values -/

@[expose] public section

namespace Silmaril.Isotope.Value

variable {α β γ : Type*}

/-- Change atomic values while retaining every runtime constructor. -/
def map (f : α → β) : Value α → Value β
  | .atom a => .atom (f a)
  | .unit => .unit
  | .pair a b => .pair (map f a) (map f b)
  | .inl a => .inl (map f a)
  | .inr a => .inr (map f a)

@[simp] theorem map_id (a : Value α) : map id a = a := by
  induction a <;> simp_all [map]

@[simp] theorem map_map (f : α → β) (g : β → γ) (a : Value α) :
    map g (map f a) = map (g ∘ f) a := by
  induction a <;> simp_all [map]

/-- Injective atomic embeddings remain injective through all value constructors. -/
theorem map_injective {f : α → β} (injective : Function.Injective f) :
    Function.Injective (map f) := by
  intro first second same
  induction first generalizing second with
  | atom a =>
    cases second <;> simp [map] at same
    exact congrArg Value.atom (injective same)
  | unit => cases second <;> simp_all [map]
  | pair a b ia ib =>
    cases second <;> simp [map] at same
    exact congrArg₂ Value.pair (ia same.1) (ib same.2)
  | inl a ih =>
    cases second <;> simp [map] at same
    exact congrArg Value.inl (ih same)
  | inr a ih =>
    cases second <;> simp [map] at same
    exact congrArg Value.inr (ih same)

/-- Equivalent atomic carriers give equivalent runtime values. -/
def equiv (e : α ≃ β) : Value α ≃ Value β where
  toFun := map e
  invFun := map e.symm
  left_inv a := by simp
  right_inv a := by simp

@[simp] theorem map_symm_map (e : α ≃ β) (a : Value α) :
    map e.symm (map e a) = a := (equiv e).symm_apply_apply a

@[simp] theorem map_map_symm (e : α ≃ β) (b : Value β) :
    map e (map e.symm b) = b := (equiv e).apply_symm_apply b

end Silmaril.Isotope.Value
