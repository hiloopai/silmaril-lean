module

public import Silmaril.Semantics.CPort.Foundations.Types.Basic.Defs
/-!
# Free type algebras for finite constructor signatures

The feature mask controls which constructors exist. Enabledness is proof data,
so its witnesses do not distinguish syntax. Products and coproducts remain
ordered binary constructors; no associativity or commutativity is imposed.
-/

@[expose] public section

namespace Silmaril

/-- The independently selectable constructors of a type signature. -/
structure TypeFeatures where
  product : Bool
  coprod : Bool
  unit : Bool
  empty : Bool
  deriving Repr, DecidableEq

namespace TypeFeatures

abbrev none : TypeFeatures := ⟨false, false, false, false⟩
abbrev productOnly : TypeFeatures := ⟨true, false, false, false⟩
abbrev coproductOnly : TypeFeatures := ⟨false, true, false, false⟩
abbrev unitOnly : TypeFeatures := ⟨false, false, true, false⟩
abbrev emptyOnly : TypeFeatures := ⟨false, false, false, true⟩
abbrev seq : TypeFeatures := ⟨true, false, true, false⟩
abbrev sum : TypeFeatures := ⟨false, true, false, true⟩
abbrev all : TypeFeatures := ⟨true, true, true, true⟩

end TypeFeatures

universe u v w x

/-- Free types over generators `α`, using exactly the enabled constructors. -/
inductive FreeTy (s : TypeFeatures) (α : Type u) : Type u where
  | base (a : α)
  | product (enabled : s.product = true) (A B : FreeTy s α)
  | coprod (enabled : s.coprod = true) (A B : FreeTy s α)
  | unit (enabled : s.unit = true)
  | empty (enabled : s.empty = true)
  deriving Repr, DecidableEq

namespace FreeTy

variable {s : TypeFeatures} {α : Type u} {β : Type v} {γ : Type w}

/-- Rename generators without changing the constructor tree. -/
def map (f : α → β) : FreeTy s α → FreeTy s β
  | .base a => .base (f a)
  | .product h A B => .product h (map f A) (map f B)
  | .coprod h A B => .coprod h (map f A) (map f B)
  | .unit h => .unit h
  | .empty h => .empty h

/-- Substitute a free type for each generator. -/
def bind : FreeTy s α → (α → FreeTy s β) → FreeTy s β
  | .base a, f => f a
  | .product h A B, f => .product h (bind A f) (bind B f)
  | .coprod h A B, f => .coprod h (bind A f) (bind B f)
  | .unit h, _ => .unit h
  | .empty h, _ => .empty h

@[simp] theorem map_base (f : α → β) (a : α) : map f (.base a : FreeTy s α) = .base (f a) := rfl
@[simp] theorem map_product (f : α → β) (h : s.product = true) (A B : FreeTy s α) :
    map f (.product h A B) = .product h (map f A) (map f B) := rfl
@[simp] theorem map_coprod (f : α → β) (h : s.coprod = true) (A B : FreeTy s α) :
    map f (.coprod h A B) = .coprod h (map f A) (map f B) := rfl
@[simp] theorem map_unit (f : α → β) (h : s.unit = true) :
    map f (.unit h) = .unit h := rfl
@[simp] theorem map_empty (f : α → β) (h : s.empty = true) :
    map f (.empty h) = .empty h := rfl

@[simp] theorem base_bind (a : α) (f : α → FreeTy s β) : bind (.base a) f = f a := rfl
@[simp] theorem product_bind (h : s.product = true) (A B : FreeTy s α) (f : α → FreeTy s β) :
    bind (.product h A B) f = .product h (bind A f) (bind B f) := rfl
@[simp] theorem coprod_bind (h : s.coprod = true) (A B : FreeTy s α) (f : α → FreeTy s β) :
    bind (.coprod h A B) f = .coprod h (bind A f) (bind B f) := rfl
@[simp] theorem unit_bind (h : s.unit = true) (f : α → FreeTy s β) :
    bind (.unit h) f = .unit h := rfl
@[simp] theorem empty_bind (h : s.empty = true) (f : α → FreeTy s β) :
    bind (.empty h) f = .empty h := rfl

@[simp] theorem map_id (t : FreeTy s α) : map id t = t := by
  induction t <;> simp_all [map]

@[simp] theorem map_map (g : β → γ) (f : α → β) (t : FreeTy s α) :
    map g (map f t) = map (g ∘ f) t := by
  induction t <;> simp_all [map]

@[simp] theorem bind_base (t : FreeTy s α) : bind t base = t := by
  induction t <;> simp_all [bind]

theorem bind_assoc (t : FreeTy s α) (f : α → FreeTy s β) (g : β → FreeTy s γ) :
    bind (bind t f) g = bind t (fun a => bind (f a) g) := by
  induction t <;> simp_all [bind]

theorem map_eq_bind (f : α → β) (t : FreeTy s α) :
    map f t = bind t (base ∘ f) := by
  induction t <;> simp_all [map, bind]

@[simp] theorem bind_map (t : FreeTy s α) (f : α → β) (g : β → FreeTy s γ) :
    bind (map f t) g = bind t (g ∘ f) := by
  induction t <;> simp_all [map, bind]

theorem map_bind (g : β → γ) (t : FreeTy s α) (f : α → FreeTy s β) :
    map g (bind t f) = bind t (fun a => map g (f a)) := by
  induction t <;> simp_all [bind]

instance : Monad (FreeTy s) where
  pure := base
  bind := bind
  map := map

instance : LawfulMonad (FreeTy s) :=
  LawfulMonad.mk' _ (id_map := map_id) (pure_bind := fun _ _ => rfl)
    (bind_assoc := bind_assoc) (bind_pure_comp := fun f t => (map_eq_bind f t).symm)

@[simp] theorem base_inj {a b : α} : (base a : FreeTy s α) = base b ↔ a = b := by
  simp only [base.injEq]

theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (map (s := s) f) := by
  intro t
  induction t with
  | base a =>
      intro t' h
      cases t' <;> simp_all [map]
      exact hf h
  | product h A B ihA ihB =>
      intro t' he
      cases t' with
      | product h' A' B' =>
          simp only [map, product.injEq] at he
          cases ihA he.1
          cases ihB he.2
          rfl
      | _ => cases he
  | coprod h A B ihA ihB =>
      intro t' he
      cases t' with
      | coprod h' A' B' =>
          simp only [map, coprod.injEq] at he
          cases ihA he.1
          cases ihB he.2
          rfl
      | _ => cases he
  | unit h => intro t' he; cases t' <;> simp_all [map]
  | empty h => intro t' he; cases t' <;> simp_all [map]

/-- An interpretation of the enabled constructors in a carrier `τ`. -/
structure Algebra (s : TypeFeatures) (τ : Type v) where
  product : s.product = true → τ → τ → τ
  coprod : s.coprod = true → τ → τ → τ
  unit : s.unit = true → τ
  empty : s.empty = true → τ

variable {τ : Type x} {σ : Type w}

/-- Extend an interpretation of generators to the free algebra. -/
def fold (alg : Algebra s τ) (f : α → τ) : FreeTy s α → τ
  | .base a => f a
  | .product h A B => alg.product h (fold alg f A) (fold alg f B)
  | .coprod h A B => alg.coprod h (fold alg f A) (fold alg f B)
  | .unit h => alg.unit h
  | .empty h => alg.empty h

@[simp] theorem fold_base (alg : Algebra s τ) (f : α → τ) (a : α) :
    fold alg f (.base a) = f a := rfl
@[simp] theorem fold_product (alg : Algebra s τ) (f : α → τ)
    (h : s.product = true) (A B : FreeTy s α) :
    fold alg f (.product h A B) = alg.product h (fold alg f A) (fold alg f B) := rfl
@[simp] theorem fold_coprod (alg : Algebra s τ) (f : α → τ)
    (h : s.coprod = true) (A B : FreeTy s α) :
    fold alg f (.coprod h A B) = alg.coprod h (fold alg f A) (fold alg f B) := rfl
@[simp] theorem fold_unit (alg : Algebra s τ) (f : α → τ) (h : s.unit = true) :
    fold alg f (.unit h) = alg.unit h := rfl
@[simp] theorem fold_empty (alg : Algebra s τ) (f : α → τ) (h : s.empty = true) :
    fold alg f (.empty h) = alg.empty h := rfl

@[simp] theorem fold_map (alg : Algebra s τ) (f : β → τ) (g : α → β) (t : FreeTy s α) :
    fold alg f (map g t) = fold alg (f ∘ g) t := by
  induction t <;> simp_all [fold, map]

theorem fold_bind (alg : Algebra s τ) (f : β → τ) (t : FreeTy s α)
    (g : α → FreeTy s β) :
    fold alg f (bind t g) = fold alg (fun a => fold alg f (g a)) t := by
  induction t <;> simp_all [fold, bind]

/-- The constructor operations make the free syntax itself an algebra. -/
def algebra : Algebra s (FreeTy s α) where
  product := product
  coprod := coprod
  unit := unit
  empty := empty

@[simp] theorem fold_algebra (t : FreeTy s α) : fold algebra base t = t := by
  induction t <;> simp_all [fold, algebra]

/-- A constructor-preserving function is uniquely determined by its action on generators. -/
theorem fold_unique (alg : Algebra s τ) (f : α → τ) (g : FreeTy s α → τ)
    (hbase : ∀ a, g (.base a) = f a)
    (hproduct : ∀ h A B, g (.product h A B) = alg.product h (g A) (g B))
    (hcoprod : ∀ h A B, g (.coprod h A B) = alg.coprod h (g A) (g B))
    (hunit : ∀ h, g (.unit h) = alg.unit h)
    (hempty : ∀ h, g (.empty h) = alg.empty h) :
    g = fold alg f := by
  funext t
  induction t <;> simp_all [fold]

/-- Constructor-preserving carrier maps commute with folding. -/
theorem fold_fusion (alg : Algebra s τ) (alg' : Algebra s σ) (f : α → τ) (g : τ → σ)
    (hproduct : ∀ h A B, g (alg.product h A B) = alg'.product h (g A) (g B))
    (hcoprod : ∀ h A B, g (alg.coprod h A B) = alg'.coprod h (g A) (g B))
    (hunit : ∀ h, g (alg.unit h) = alg'.unit h)
    (hempty : ∀ h, g (alg.empty h) = alg'.empty h) (t : FreeTy s α) :
    g (fold alg f t) = fold alg' (g ∘ f) t := by
  induction t <;> simp_all [fold]

end FreeTy

end Silmaril
