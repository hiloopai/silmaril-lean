module

public import Silmaril.Semantics.CPort.Foundations.Types.Concrete.Defs
public import Silmaril.Semantics.CPort.Foundations.Types.Inclusion.Defs
public import Mathlib.Logic.Equiv.Defs

/-!
# Concrete and signature-indexed type syntax

The ordinary `Ty` syntax is equivalent to `FreeTy` with all four constructors
enabled. The explicit conversions preserve renaming, substitution, and folding.
-/

@[expose] public section

universe u v

namespace Silmaril

variable {s : TypeFeatures} {α : Type u} {β : Type v}

namespace Ty

/-- Regard ordinary type syntax as free syntax with every constructor enabled. -/
@[simp] def toFree : Ty α → FreeTy TypeFeatures.all α
  | .base a => .base a
  | .product A B => .product rfl (toFree A) (toFree B)
  | .unit => .unit rfl
  | .coprod A B => .coprod rfl (toFree A) (toFree B)
  | .empty => .empty rfl

/-- An ordinary type algebra can interpret any subset of its constructors. -/
def Algebra.toFree {τ : Type v} (alg : Algebra τ) : FreeTy.Algebra s τ where
  product := fun _ => alg.product
  coprod := fun _ => alg.coprod
  unit := fun _ => alg.unit
  empty := fun _ => alg.empty

@[simp] theorem toFree_map (f : α → β) (A : Ty α) :
    toFree (map f A) = FreeTy.map f (toFree A) := by
  induction A <;> simp_all

@[simp] theorem toFree_bind (A : Ty α) (f : α → Ty β) :
    toFree (bind A f) = FreeTy.bind (toFree A) (fun a => toFree (f a)) := by
  induction A <;> simp_all

@[simp] theorem fold_toFree {τ : Type v} (alg : Algebra τ) (f : α → τ) (A : Ty α) :
    FreeTy.fold alg.toFree f (toFree A) = fold alg f A := by
  induction A <;> simp_all [Algebra.toFree]

end Ty

namespace FreeTy

/-- Include any constructor signature in the ordinary full type syntax. -/
@[simp] def toTy : FreeTy s α → Ty α
  | .base a => .base a
  | .product _ A B => .product (toTy A) (toTy B)
  | .coprod _ A B => .coprod (toTy A) (toTy B)
  | .unit _ => .unit
  | .empty _ => .empty

instance : CoeOut (FreeTy s α) (Ty α) := ⟨toTy⟩

/-- Enlarging a signature before entering full syntax does not change the result. -/
@[simp] theorem toTy_embed {t : TypeFeatures} (h : TypeFeatures.Inclusion s t)
    (A : FreeTy s α) : toTy (embed h A) = toTy A := by
  induction A <;> simp_all [embed]

/-- Passing through concrete syntax agrees with the canonical inclusion into full syntax. -/
theorem toFree_toTy_eq_embed (A : FreeTy s α) :
    Ty.toFree (toTy A) = embed (TypeFeatures.Inclusion.toAll s) A := by
  induction A <;> simp_all [embed]

@[simp] theorem toTy_map (f : α → β) (A : FreeTy s α) :
    toTy (map f A) = Ty.map f (toTy A) := by
  induction A <;> simp_all

@[simp] theorem toTy_bind (A : FreeTy s α) (f : α → FreeTy s β) :
    toTy (bind A f) = Ty.bind (toTy A) (fun a => toTy (f a)) := by
  induction A <;> simp_all

@[simp] theorem fold_toTy {τ : Type v} (alg : Ty.Algebra τ) (f : α → τ)
    (A : FreeTy s α) :
    Ty.fold alg f (toTy A) = fold alg.toFree f A := by
  induction A <;> simp_all [Ty.Algebra.toFree]

@[simp] theorem toTy_toFree (A : Ty α) : toTy (Ty.toFree A) = A := by
  induction A <;> simp_all

@[simp] theorem toFree_toTy (A : FreeTy TypeFeatures.all α) : Ty.toFree (toTy A) = A := by
  induction A <;> simp_all

theorem toTy_injective : Function.Injective (@toTy s α) := by
  suffices h : ∀ A B : FreeTy s α, toTy A = toTy B ↔ A = B from fun {A B} => (h A B).mp
  intro A B
  induction A generalizing B <;> cases B <;> simp_all

end FreeTy

namespace Ty

theorem toFree_injective : Function.Injective (@toFree α) := by
  intro A B h
  simpa only [FreeTy.toTy_toFree] using congrArg FreeTy.toTy h

/-- Concrete full type syntax and full signature-indexed syntax agree. -/
def freeEquiv : Ty α ≃ FreeTy TypeFeatures.all α where
  toFun := toFree
  invFun := FreeTy.toTy
  left_inv := FreeTy.toTy_toFree
  right_inv := FreeTy.toFree_toTy

end Ty

end Silmaril
