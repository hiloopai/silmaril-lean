module

public import Silmaril.Semantics.CPort.Foundations.Types.Free.Defs
/-!
# Inclusions and interpretations of free type signatures

Inclusions preserve constructor trees and only enlarge the available signature.
Their witnesses are propositions, so embeddings do not depend on an inclusion
proof or on a path through intermediate signatures. The named coercions follow
the singleton-to-bundle-to-full paths; arbitrary inclusions remain explicit.
Generator injection is written `pure a` or `.base a`, so inserting a whole tree
as one generator remains distinct from mapping an injection over its leaves.
-/

@[expose] public section

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
