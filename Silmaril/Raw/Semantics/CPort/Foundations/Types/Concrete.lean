module

public import Silmaril.Semantics.CPort.Foundations.Types.Basic.Defs
public import Init.Control.Lawful

/-!
# Simple type syntax

`Ty α` freely adjoins binary products, binary coproducts, a unit, and an empty
type to base types `α`. Its monad substitutes type expressions for base types;
`fold` interprets the constructors without imposing equations on them.
-/

@[expose] public section

universe u v w

namespace Silmaril

/-- Simple types freely generated from base types `α`. -/
inductive Ty (α : Type u) : Type u where
  | base (a : α)
  | product (A B : Ty α)
  | unit
  | coprod (A B : Ty α)
  | empty
  deriving Repr, DecidableEq

variable {α : Type u} {β : Type v} {γ : Type w}

instance : TypeFormers (Ty α) where
  product := Ty.product
  unit := Ty.unit
  coprod := Ty.coprod
  empty := Ty.empty

@[simp] theorem product_ty (A B : Ty α) : product A B = Ty.product A B := rfl
@[simp] theorem unit_ty : (unit : Ty α) = Ty.unit := rfl
@[simp] theorem coprod_ty (A B : Ty α) : coprod A B = Ty.coprod A B := rfl
@[simp] theorem empty_ty : (empty : Ty α) = Ty.empty := rfl

namespace Ty

theorem base_injective : Function.Injective (@base α) := fun _ _ h => base.inj h

/-- Rename the base types, preserving every type constructor. -/
@[simp] def map (f : α → β) : Ty α → Ty β
  | .base a => .base (f a)
  | .product A B => .product (map f A) (map f B)
  | .unit => .unit
  | .coprod A B => .coprod (map f A) (map f B)
  | .empty => .empty

/-- Substitute a type expression for each base type. -/
@[simp] def bind (A : Ty α) (f : α → Ty β) : Ty β :=
  match A with
  | .base a => f a
  | .product A B => .product (bind A f) (bind B f)
  | .unit => .unit
  | .coprod A B => .coprod (bind A f) (bind B f)
  | .empty => .empty

@[simp] theorem map_id (A : Ty α) : map id A = A := by
  induction A <;> simp_all

@[simp] theorem map_map (g : β → γ) (f : α → β) (A : Ty α) :
    map g (map f A) = map (g ∘ f) A := by
  induction A <;> simp_all

@[simp] theorem bind_base (A : Ty α) : bind A base = A := by
  induction A <;> simp_all

@[simp] theorem bind_assoc (A : Ty α) (f : α → Ty β) (g : β → Ty γ) :
    bind (bind A f) g = bind A (fun a => bind (f a) g) := by
  induction A <;> simp_all

@[simp] theorem bind_base_map (A : Ty α) (f : α → β) :
    bind A (fun a => base (f a)) = map f A := by
  induction A <;> simp_all

@[simp] theorem map_bind (A : Ty α) (f : α → Ty β) (g : β → γ) :
    map g (bind A f) = bind A (fun a => map g (f a)) := by
  induction A <;> simp_all

@[simp] theorem bind_map (A : Ty α) (f : α → β) (g : β → Ty γ) :
    bind (map f A) g = bind A (g ∘ f) := by
  induction A <;> simp_all

theorem map_injective (f : α → β) (hf : Function.Injective f) :
    Function.Injective (map f) := by
  suffices h : ∀ A B : Ty α, map f A = map f B ↔ A = B from fun {A B} => (h A B).mp
  intro A B
  induction A generalizing B <;> cases B <;> simp_all [hf.eq_iff]

instance : Monad Ty where
  pure := base
  map := map
  bind := bind

instance : LawfulMonad Ty := LawfulMonad.mk' Ty
  (id_map := fun A => map_id A)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun A f g => bind_assoc A f g)
  (bind_pure_comp := fun f A => bind_base_map A f)

/-- An interpretation of the four type constructors on a carrier. -/
structure Algebra (τ : Type v) where
  product : τ → τ → τ
  unit : τ
  coprod : τ → τ → τ
  empty : τ

namespace Algebra

/-- Every full type-former interface supplies an algebra for `Ty`. -/
def ofTypeFormers (τ : Type v) [TypeFormers τ] : Algebra τ where
  product := Silmaril.product
  unit := Silmaril.unit
  coprod := Silmaril.coprod
  empty := Silmaril.empty

end Algebra

/-- Interpret base types and recursively interpret the type constructors. -/
@[simp] def fold {τ : Type v} (alg : Algebra τ) (f : α → τ) : Ty α → τ
  | .base a => f a
  | .product A B => alg.product (fold alg f A) (fold alg f B)
  | .unit => alg.unit
  | .coprod A B => alg.coprod (fold alg f A) (fold alg f B)
  | .empty => alg.empty

@[simp] theorem fold_map {τ : Type w} (alg : Algebra τ) (f : β → τ)
    (g : α → β) (A : Ty α) :
    fold alg f (map g A) = fold alg (f ∘ g) A := by
  induction A <;> simp_all

@[simp] theorem fold_bind {τ : Type w} (alg : Algebra τ) (f : β → τ)
    (g : α → Ty β) (A : Ty α) :
    fold alg f (bind A g) = fold alg (fun a => fold alg f (g a)) A := by
  induction A <;> simp_all

@[simp] theorem fold_base (A : Ty α) :
    fold (Algebra.ofTypeFormers (Ty α)) base A = A := by
  induction A <;> simp_all [Algebra.ofTypeFormers]

/-- An interpretation is determined by its action on each constructor. -/
theorem fold_unique {τ : Type v} (alg : Algebra τ) (f : α → τ) (h : Ty α → τ)
    (hbase : ∀ a, h (.base a) = f a)
    (hproduct : ∀ A B, h (.product A B) = alg.product (h A) (h B))
    (hunit : h .unit = alg.unit)
    (hcoprod : ∀ A B, h (.coprod A B) = alg.coprod (h A) (h B))
    (hempty : h .empty = alg.empty) : h = fold alg f := by
  funext A
  induction A <;> simp_all

/-- Constructor-preserving maps commute with interpretation. -/
theorem fold_fusion {τ : Type v} {σ : Type w} (alg : Algebra τ) (alg' : Algebra σ)
    (f : α → τ) (g : τ → σ)
    (hproduct : ∀ A B, g (alg.product A B) = alg'.product (g A) (g B))
    (hunit : g alg.unit = alg'.unit)
    (hcoprod : ∀ A B, g (alg.coprod A B) = alg'.coprod (g A) (g B))
    (hempty : g alg.empty = alg'.empty) (A : Ty α) :
    g (fold alg f A) = fold alg' (g ∘ f) A := by
  induction A <;> simp_all

end Ty

end Silmaril
