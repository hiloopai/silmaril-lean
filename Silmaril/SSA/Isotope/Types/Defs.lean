module

public import Init.Control.Lawful

/-!
# Simple type syntax and instruction interfaces

Type-former capabilities (`HasProduct`, `TypeFormers`, …), the concrete type
syntax `Ty`, the signature-indexed free type syntax `FreeTy` with its feature
inclusions, and the instruction interfaces `HasTy`, `HasEff` and `Signature`
that lambda-SSA typing is stated with. The comparison of `Ty` with `FreeTy`
and the monad-homomorphism certificates are in `Silmaril.SSA.Isotope.Types.Thms`.
-/

@[expose] public section

/-!
# Type-former capabilities

Each capability supplies an operation on type codes. Semantic laws and
interpretations are separate; the bundles only collect operations.
-/


universe u

namespace Silmaril

class HasProduct (τ : Type u) where
  product : τ → τ → τ

class HasCoproduct (τ : Type u) where
  coprod : τ → τ → τ

class HasUnit (τ : Type u) where
  unit : τ

class HasEmpty (τ : Type u) where
  empty : τ

/-- Binary products and their unit, sufficient for sequential type syntax. -/
class ProductTypeFormers (τ : Type u) extends HasProduct τ, HasUnit τ

/-- Binary coproducts and the empty type. -/
class CoproductTypeFormers (τ : Type u) extends HasCoproduct τ, HasEmpty τ

/-- The full signature used by SSA and let-iter. -/
class TypeFormers (τ : Type u) extends ProductTypeFormers τ, CoproductTypeFormers τ

variable {τ : Type u}

def product [HasProduct τ] (A B : τ) : τ := HasProduct.product A B
def coprod [HasCoproduct τ] (A B : τ) : τ := HasCoproduct.coprod A B
def unit [HasUnit τ] : τ := HasUnit.unit
def empty [HasEmpty τ] : τ := HasEmpty.empty

namespace TypeFormers

export HasProduct (product)
export HasCoproduct (coprod)
export HasUnit (unit)
export HasEmpty (empty)

end TypeFormers

end Silmaril

end

@[expose] public section

/-!
# Free type algebras for finite constructor signatures

The feature mask controls which constructors exist. Enabledness is proof data,
so its witnesses do not distinguish syntax. Products and coproducts remain
ordered binary constructors; no associativity or commutativity is imposed.
-/


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

end

@[expose] public section

/-!
# Simple type syntax

`Ty α` freely adjoins binary products, binary coproducts, a unit, and an empty
type to base types `α`. Its monad substitutes type expressions for base types;
`fold` interprets the constructors without imposing equations on them.
-/


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

end

@[expose] public section

/-!
# Inclusions and interpretations of free type signatures

Inclusions preserve constructor trees and only enlarge the available signature.
Their witnesses are propositions, so embeddings do not depend on an inclusion
proof or on a path through intermediate signatures. The named coercions follow
the singleton-to-bundle-to-full paths; arbitrary inclusions remain explicit.
Generator injection is written `pure a` or `.base a`, so inserting a whole tree
as one generator remains distinct from mapping an injection over its leaves.
-/


namespace Silmaril

namespace TypeFeatures

/-- Every constructor enabled in `s` is also enabled in `t`. -/
structure Inclusion (s t : TypeFeatures) : Prop where
  product : s.product = true → t.product = true
  coprod : s.coprod = true → t.coprod = true
  unit : s.unit = true → t.unit = true
  empty : s.empty = true → t.empty = true

namespace Inclusion

variable {r s t : TypeFeatures}

protected theorem refl (s : TypeFeatures) : Inclusion s s := ⟨id, id, id, id⟩

protected theorem trans (h : Inclusion r s) (k : Inclusion s t) : Inclusion r t :=
  ⟨k.product ∘ h.product, k.coprod ∘ h.coprod, k.unit ∘ h.unit, k.empty ∘ h.empty⟩

theorem fromNone (s : TypeFeatures) : Inclusion none s := by
  constructor <;> intro h <;> cases h

theorem toAll (s : TypeFeatures) : Inclusion s all :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem productToSeq : Inclusion productOnly seq := by
  constructor <;> intro h <;> first | rfl | cases h

theorem unitToSeq : Inclusion unitOnly seq := by
  constructor <;> intro h <;> first | rfl | cases h

theorem coproductToSum : Inclusion coproductOnly sum := by
  constructor <;> intro h <;> first | rfl | cases h

theorem emptyToSum : Inclusion emptyOnly sum := by
  constructor <;> intro h <;> first | rfl | cases h

theorem seqToAll : Inclusion seq all := toAll seq
theorem sumToAll : Inclusion sum all := toAll sum

/-- A coproduct signature cannot be embedded into the sequential signature. -/
theorem not_coproductToSeq : ¬ Inclusion coproductOnly seq := fun h =>
  Bool.noConfusion (h.coprod rfl)

end Inclusion
end TypeFeatures

universe u v w

namespace FreeTy

variable {r s t : TypeFeatures} {α : Type u} {β : Type v} {τ : Type w}

/-- Enlarge the constructor signature, preserving generators and tree shape. -/
def embed (h : TypeFeatures.Inclusion s t) : FreeTy s α → FreeTy t α
  | .base a => .base a
  | .product enabled A B => .product (h.product enabled) (embed h A) (embed h B)
  | .coprod enabled A B => .coprod (h.coprod enabled) (embed h A) (embed h B)
  | .unit enabled => .unit (h.unit enabled)
  | .empty enabled => .empty (h.empty enabled)

@[simp] theorem embed_base (h : TypeFeatures.Inclusion s t) (a : α) :
    embed h (.base a) = .base a := rfl

@[simp] theorem embed_product (h : TypeFeatures.Inclusion s t)
    (enabled : s.product = true) (A B : FreeTy s α) :
    embed h (.product enabled A B) = .product (h.product enabled) (embed h A) (embed h B) := rfl

@[simp] theorem embed_coprod (h : TypeFeatures.Inclusion s t)
    (enabled : s.coprod = true) (A B : FreeTy s α) :
    embed h (.coprod enabled A B) = .coprod (h.coprod enabled) (embed h A) (embed h B) := rfl

@[simp] theorem embed_unit (h : TypeFeatures.Inclusion s t) (enabled : s.unit = true) :
    embed h (.unit enabled : FreeTy s α) = .unit (h.unit enabled) := rfl

@[simp] theorem embed_empty (h : TypeFeatures.Inclusion s t) (enabled : s.empty = true) :
    embed h (.empty enabled : FreeTy s α) = .empty (h.empty enabled) := rfl

theorem embed_proof_irrel (h k : TypeFeatures.Inclusion s t) (A : FreeTy s α) :
    embed h A = embed k A := rfl

@[simp] theorem embed_refl (A : FreeTy s α) : embed (.refl s) A = A := by
  induction A <;> simp_all [embed]

@[simp] theorem embed_embed (h : TypeFeatures.Inclusion r s)
    (k : TypeFeatures.Inclusion s t) (A : FreeTy r α) :
    embed k (embed h A) = embed (h.trans k) A := by
  induction A <;> simp_all [embed]

/-- Any two paths between the same signatures induce the same embedding. -/
theorem embed_path_independent {s' : TypeFeatures}
    (h : TypeFeatures.Inclusion r s) (k : TypeFeatures.Inclusion s t)
    (h' : TypeFeatures.Inclusion r s') (k' : TypeFeatures.Inclusion s' t)
    (A : FreeTy r α) : embed k (embed h A) = embed k' (embed h' A) := by
  simp only [embed_embed]

theorem embed_injective (h : TypeFeatures.Inclusion s t) :
    Function.Injective (embed (α := α) h) := by
  intro A
  induction A with
  | base a => intro B he; cases B <;> simp_all [embed]
  | product enabled A B ihA ihB =>
      intro C he
      cases C with
      | product enabled' A' B' =>
          simp only [embed, product.injEq] at he
          exact congr (congrArg (product enabled) (ihA he.1)) (ihB he.2)
      | _ => cases he
  | coprod enabled A B ihA ihB =>
      intro C he
      cases C with
      | coprod enabled' A' B' =>
          simp only [embed, coprod.injEq] at he
          exact congr (congrArg (coprod enabled) (ihA he.1)) (ihB he.2)
      | _ => cases he
  | unit enabled => intro B he; cases B <;> simp_all [embed]
  | empty enabled => intro B he; cases B <;> simp_all [embed]

@[simp] theorem embed_eq_embed (h : TypeFeatures.Inclusion s t) (A B : FreeTy s α) :
    embed h A = embed h B ↔ A = B := ⟨fun he => embed_injective h he, congrArg (embed h)⟩

@[simp] theorem embed_map (h : TypeFeatures.Inclusion s t) (f : α → β) (A : FreeTy s α) :
    embed h (map f A) = map f (embed h A) := by
  induction A <;> simp_all [embed, map]

@[simp] theorem embed_pure (h : TypeFeatures.Inclusion s t) (a : α) :
    embed h (pure a) = (pure a : FreeTy t α) := rfl

@[simp] theorem embed_bind (h : TypeFeatures.Inclusion s t) (A : FreeTy s α)
    (f : α → FreeTy s β) :
    embed h (bind A f) = bind (embed h A) (fun a => embed h (f a)) := by
  induction A <;> simp_all [embed, bind]

/-- Forget operations that are absent from the smaller signature. -/
def Algebra.restrict (alg : Algebra t τ) (h : TypeFeatures.Inclusion s t) : Algebra s τ where
  product := fun enabled => alg.product (h.product enabled)
  coprod := fun enabled => alg.coprod (h.coprod enabled)
  unit := fun enabled => alg.unit (h.unit enabled)
  empty := fun enabled => alg.empty (h.empty enabled)

@[simp] theorem Algebra.restrict_refl (alg : Algebra s τ) : alg.restrict (.refl s) = alg := rfl

@[simp] theorem Algebra.restrict_restrict (alg : Algebra t τ)
    (h : TypeFeatures.Inclusion r s) (k : TypeFeatures.Inclusion s t) :
    (alg.restrict k).restrict h = alg.restrict (h.trans k) := rfl

@[simp] theorem fold_embed (alg : Algebra t τ) (f : α → τ)
    (h : TypeFeatures.Inclusion s t) (A : FreeTy s α) :
    fold alg f (embed h A) = fold (alg.restrict h) f A := by
  induction A <;> simp_all [embed, fold, Algebra.restrict]

end FreeTy

/-- Free binary-product syntax, without a unit. -/
abbrev ProductTy (α : Type u) := FreeTy TypeFeatures.productOnly α
/-- Free binary-coproduct syntax, without an empty type. -/
abbrev CoproductTy (α : Type u) := FreeTy TypeFeatures.coproductOnly α
abbrev UnitTy (α : Type u) := FreeTy TypeFeatures.unitOnly α
abbrev EmptyTy (α : Type u) := FreeTy TypeFeatures.emptyOnly α
/-- Free sequential type syntax: products and their unit. -/
abbrev SeqTy (α : Type u) := FreeTy TypeFeatures.seq α
/-- Free sum type syntax: coproducts and the empty type. -/
abbrev SumTy (α : Type u) := FreeTy TypeFeatures.sum α
/-- Free syntax for all four type formers. -/
abbrev FullTy (α : Type u) := FreeTy TypeFeatures.all α

namespace FreeTy

variable {α : Type u} {τ : Type v}

instance : Coe (ProductTy α) (SeqTy α) := ⟨embed .productToSeq⟩
instance : Coe (UnitTy α) (SeqTy α) := ⟨embed .unitToSeq⟩
instance : Coe (CoproductTy α) (SumTy α) := ⟨embed .coproductToSum⟩
instance : Coe (EmptyTy α) (SumTy α) := ⟨embed .emptyToSum⟩
instance : Coe (SeqTy α) (FullTy α) := ⟨embed .seqToAll⟩
instance : Coe (SumTy α) (FullTy α) := ⟨embed .sumToAll⟩

theorem coe_product_full (A : ProductTy α) :
    ((A : SeqTy α) : FullTy α) = embed (.toAll _) A := by
  exact embed_embed .productToSeq .seqToAll A

theorem coe_unit_full (A : UnitTy α) :
    ((A : SeqTy α) : FullTy α) = embed (.toAll _) A := by
  exact embed_embed .unitToSeq .seqToAll A

theorem coe_coproduct_full (A : CoproductTy α) :
    ((A : SumTy α) : FullTy α) = embed (.toAll _) A := by
  exact embed_embed .coproductToSum .sumToAll A

theorem coe_empty_full (A : EmptyTy α) :
    ((A : SumTy α) : FullTy α) = embed (.toAll _) A := by
  exact embed_embed .emptyToSum .sumToAll A

/-- Only enabled constructors supply capabilities; disabled operations have no instance. -/
instance {c u e : Bool} : HasProduct (FreeTy ⟨true, c, u, e⟩ α) := ⟨product rfl⟩
instance {p u e : Bool} : HasCoproduct (FreeTy ⟨p, true, u, e⟩ α) := ⟨coprod rfl⟩
instance {p c e : Bool} : HasUnit (FreeTy ⟨p, c, true, e⟩ α) := ⟨unit rfl⟩
instance {p c u : Bool} : HasEmpty (FreeTy ⟨p, c, u, true⟩ α) := ⟨empty rfl⟩

instance {c e : Bool} : ProductTypeFormers (FreeTy ⟨true, c, true, e⟩ α) where
  toHasProduct := inferInstance
  toHasUnit := inferInstance

instance {p u : Bool} : CoproductTypeFormers (FreeTy ⟨p, true, u, true⟩ α) where
  toHasCoproduct := inferInstance
  toHasEmpty := inferInstance

instance : TypeFormers (FullTy α) where
  product := product rfl
  coprod := coprod rfl
  unit := unit rfl
  empty := empty rfl

namespace Algebra

/-- Interpreting bare generators requires no constructor operations. -/
def ofNone : Algebra TypeFeatures.none τ where
  product := fun h => nomatch h
  coprod := fun h => nomatch h
  unit := fun h => nomatch h
  empty := fun h => nomatch h

def ofProduct [HasProduct τ] : Algebra TypeFeatures.productOnly τ where
  product := fun _ => Silmaril.product
  coprod := fun h => nomatch h
  unit := fun h => nomatch h
  empty := fun h => nomatch h

def ofCoproduct [HasCoproduct τ] : Algebra TypeFeatures.coproductOnly τ where
  product := fun h => nomatch h
  coprod := fun _ => Silmaril.coprod
  unit := fun h => nomatch h
  empty := fun h => nomatch h

def ofUnit [HasUnit τ] : Algebra TypeFeatures.unitOnly τ where
  product := fun h => nomatch h
  coprod := fun h => nomatch h
  unit := fun _ => Silmaril.unit
  empty := fun h => nomatch h

def ofEmpty [HasEmpty τ] : Algebra TypeFeatures.emptyOnly τ where
  product := fun h => nomatch h
  coprod := fun h => nomatch h
  unit := fun h => nomatch h
  empty := fun _ => Silmaril.empty

def ofSeq [HasProduct τ] [HasUnit τ] : Algebra TypeFeatures.seq τ where
  product := fun _ => Silmaril.product
  coprod := fun h => nomatch h
  unit := fun _ => Silmaril.unit
  empty := fun h => nomatch h

def ofSum [HasCoproduct τ] [HasEmpty τ] : Algebra TypeFeatures.sum τ where
  product := fun h => nomatch h
  coprod := fun _ => Silmaril.coprod
  unit := fun h => nomatch h
  empty := fun _ => Silmaril.empty

def ofAll [HasProduct τ] [HasCoproduct τ] [HasUnit τ] [HasEmpty τ] :
    Algebra TypeFeatures.all τ where
  product := fun _ => Silmaril.product
  coprod := fun _ => Silmaril.coprod
  unit := fun _ => Silmaril.unit
  empty := fun _ => Silmaril.empty

end Algebra

/-- Enlarging a sequential type never introduces a coproduct at its root. -/
theorem seq_coe_ne_coprod (A : SeqTy α) (B C : FullTy α) :
    (A : FullTy α) ≠ .coprod rfl B C := by
  cases A with
  | coprod h _ _ => cases h
  | empty h => cases h
  | _ => intro h; cases h

/-- In particular, the two routes from the empty signature agree. -/
theorem empty_signature_diamond (A : FreeTy TypeFeatures.none α) :
    embed .seqToAll (embed (.fromNone _) A) =
      embed .sumToAll (embed (.fromNone _) A) :=
  embed_path_independent (.fromNone _) .seqToAll (.fromNone _) .sumToAll A

end FreeTy
end Silmaril

end

@[expose] public section

/-!
# Instruction interfaces

Typing and effects are independent. A signature may supply either interface;
`Signature` bundles both without adding a purity requirement or effect laws.
-/


universe u v w

namespace Silmaril

class HasTy (Φ : Type u) (τ : Type v) where
  src : Φ → τ
  trg : Φ → τ

class HasEff (Φ : Type u) (ε : Type v) where
  eff : Φ → ε

class Signature (Φ : Type u) (τ : Type v) (ε : Type w)
    extends HasTy Φ τ, HasEff Φ ε

variable {Φ : Type u} {τ : Type v} {ε : Type w}

def instrSrc [HasTy Φ τ] (f : Φ) : τ := HasTy.src f
def instrTrg [HasTy Φ τ] (f : Φ) : τ := HasTy.trg f
def instrEff [HasEff Φ ε] (f : Φ) : ε := HasEff.eff f

/-- Primitive purity relative to a chosen effect; independent of typing. -/
def IsPure [HasEff Φ ε] (pureEff : ε) (f : Φ) : Prop := instrEff f = pureEff

end Silmaril

end
