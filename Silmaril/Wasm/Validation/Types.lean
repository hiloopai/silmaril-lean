module

public import Silmaril.Wasm.Types

@[expose] public section

/-! # Validation conditions for Core source types

This module checks source type-index scope, limits, and the structural side
conditions on recursive groups. `RecType.StructurallyValid` deliberately does
not check composite-type matching against a declared supertype: that requires
closing and unrolling recursive defined types. It is not a complete recursive
type validator.

The abstract heap hierarchy is complete on abstract heap types. Reference and
field matching are parameterized by the underlying matching relation, so this
layer does not substitute nominal index equality for recursive type matching.

See [type validation](https://webassembly.github.io/spec/core/valid/types.html)
and [matching](https://webassembly.github.io/spec/core/valid/matching.html).
-/

namespace Silmaril.Wasm

def HeapType.Scoped (typeCount : Nat) : HeapType → Prop
  | .abstract _ => True
  | .typeIdx i => i.toNat < typeCount

instance (n : Nat) (t : HeapType) : Decidable (t.Scoped n) := by
  cases t <;> unfold HeapType.Scoped <;> infer_instance

def RefType.Scoped (n : Nat) (t : RefType) : Prop := t.heap.Scoped n

instance (n : Nat) (t : RefType) : Decidable (t.Scoped n) :=
  inferInstanceAs (Decidable (t.heap.Scoped n))

def ValType.Scoped (n : Nat) : ValType → Prop
  | .num _ | .vec _ => True
  | .ref t => t.Scoped n

instance (n : Nat) (t : ValType) : Decidable (t.Scoped n) := by
  cases t <;> unfold ValType.Scoped <;> infer_instance

def ResultType.Scoped (n : Nat) (ts : ResultType) : Prop :=
  ∀ t ∈ ts, t.Scoped n

instance (n : Nat) (ts : ResultType) : Decidable (ResultType.Scoped n ts) :=
  inferInstanceAs (Decidable (∀ t ∈ ts, t.Scoped n))

def StorageType.Scoped (n : Nat) : StorageType → Prop
  | .val t => t.Scoped n
  | .packed _ => True

instance (n : Nat) (t : StorageType) : Decidable (t.Scoped n) := by
  cases t <;> unfold StorageType.Scoped <;> infer_instance

def FieldType.Scoped (n : Nat) (t : FieldType) : Prop := t.storage.Scoped n

instance (n : Nat) (t : FieldType) : Decidable (t.Scoped n) :=
  inferInstanceAs (Decidable (t.storage.Scoped n))

def FuncType.Scoped (n : Nat) (t : FuncType) : Prop :=
  ResultType.Scoped n t.params ∧ ResultType.Scoped n t.results

instance (n : Nat) (t : FuncType) : Decidable (t.Scoped n) :=
  inferInstanceAs (Decidable (ResultType.Scoped n t.params ∧ ResultType.Scoped n t.results))

def CompositeType.Scoped (n : Nat) : CompositeType → Prop
  | .func t => t.Scoped n
  | .struct fields => ∀ f ∈ fields, f.Scoped n
  | .array field => field.Scoped n

instance (n : Nat) (t : CompositeType) : Decidable (t.Scoped n) := by
  cases t <;> unfold CompositeType.Scoped <;> infer_instance

/-- A declared supertype must exist, precede the current type, and be extensible. -/
def SubType.ParentAllowed (types : List SubType) (current : Nat) (i : TypeIdx) : Prop :=
  i.toNat < current ∧ match types[i.toNat]? with
    | none => False
    | some parent => parent.final_ = false

instance (ts : List SubType) (current : Nat) (i : TypeIdx) :
    Decidable (SubType.ParentAllowed ts current i) := by
  unfold SubType.ParentAllowed
  cases ts[i.toNat]? <;> infer_instance

/-- Necessary structural conditions, excluding recursive composite matching. -/
def SubType.StructurallyValid (types : List SubType) (current : Nat) (t : SubType) : Prop :=
  t.body.Scoped types.length ∧ t.supertypes.length ≤ 1 ∧
    ∀ i ∈ t.supertypes, ParentAllowed types current i

instance (ts : List SubType) (current : Nat) (t : SubType) :
    Decidable (t.StructurallyValid ts current) := by
  unfold SubType.StructurallyValid
  infer_instance

/-- All members see the entire group for recursive references; supertype edges
still point strictly backwards in the combined type-index space. Empty groups
are accepted, as in the declarative source validation rule. -/
def RecType.StructurallyValid (previous : List SubType) (group : RecType) : Prop :=
  ∀ i : Fin group.types.length,
    (group.types[i]).StructurallyValid (previous ++ group.types) (previous.length + i.val)

instance (previous : List SubType) (group : RecType) :
    Decidable (group.StructurallyValid previous) := by
  unfold RecType.StructurallyValid
  infer_instance

def RecType.checkStructure (previous : List SubType) (group : RecType) : Bool :=
  decide (group.StructurallyValid previous)

@[simp] theorem RecType.checkStructure_eq_true (previous : List SubType) (group : RecType) :
    group.checkStructure previous = true ↔ group.StructurallyValid previous := by
  simp [checkStructure]

theorem SubType.StructurallyValid.supertype_before {types : List SubType} {current : Nat}
    {t : SubType} (h : t.StructurallyValid types current) {i : TypeIdx}
    (hi : i ∈ t.supertypes) : i.toNat < current := (h.2.2 i hi).1

theorem SubType.StructurallyValid.supertype_not_final {types : List SubType} {current : Nat}
    {t parent : SubType} (h : t.StructurallyValid types current) {i : TypeIdx}
    (hi : i ∈ t.supertypes) (hp : types[i.toNat]? = some parent) : parent.final_ = false := by
  have allowed := (h.2.2 i hi).2
  simpa [hp] using allowed

/-- Address width used to validate memory and table limits. -/
def AddrType.width (t : AddrType) : Nat := t.intType.width

/-- Inclusive upper bound, with minimum no greater than an optional maximum. -/
def Limits.Valid (bound : Nat) (limits : Limits) : Prop :=
  limits.min.val ≤ bound ∧ match limits.max with
    | none => True
    | some max => limits.min.val ≤ max.val ∧ max.val ≤ bound

instance (bound : Nat) (limits : Limits) : Decidable (limits.Valid bound) := by
  unfold Limits.Valid
  cases limits.max <;> infer_instance

def Limits.check (bound : Nat) (limits : Limits) : Bool := decide (limits.Valid bound)

@[simp] theorem Limits.check_eq_true (bound : Nat) (limits : Limits) :
    limits.check bound = true ↔ limits.Valid bound := by simp [check]

theorem Limits.Valid.min_le {bound : Nat} {limits : Limits} (h : limits.Valid bound) :
    limits.min.val ≤ bound := h.1

theorem Limits.Valid.max_bounds {bound : Nat} {limits : Limits}
    (h : limits.Valid bound) {max : Fin (2 ^ 64)} (hm : limits.max = some max) :
    limits.min.val ≤ max.val ∧ max.val ≤ bound := by
  simpa [hm] using h.2

def MemoryType.Valid (t : MemoryType) : Prop :=
  t.limits.Valid (2 ^ (t.address.width - 16))

instance (t : MemoryType) : Decidable t.Valid :=
  inferInstanceAs (Decidable (t.limits.Valid (2 ^ (t.address.width - 16))))

def TableType.Valid (typeCount : Nat) (t : TableType) : Prop :=
  t.limits.Valid (2 ^ t.address.width - 1) ∧ t.element.Scoped typeCount

instance (n : Nat) (t : TableType) : Decidable (t.Valid n) := by
  unfold TableType.Valid
  infer_instance

def GlobalType.Valid (typeCount : Nat) (t : GlobalType) : Prop := t.value.Scoped typeCount

instance (n : Nat) (t : GlobalType) : Decidable (t.Valid n) :=
  inferInstanceAs (Decidable (t.value.Scoped n))

/-- The four disjoint abstract heap hierarchies, including their bottom types. -/
def AbsHeapType.matches (a b : AbsHeapType) : Bool :=
  decide (a = b) || match a, b with
    | .eq, .any | .i31, .eq | .i31, .any
    | .struct, .eq | .struct, .any | .array, .eq | .array, .any
    | .none, .i31 | .none, .struct | .none, .array | .none, .eq | .none, .any
    | .nofunc, .func | .noexn, .exn | .noextern, .extern => true
    | _, _ => false

def AbsHeapType.Matches (a b : AbsHeapType) : Prop := a.matches b = true

instance (a b : AbsHeapType) : Decidable (a.Matches b) :=
  inferInstanceAs (Decidable (a.matches b = true))

@[refl] theorem AbsHeapType.Matches.refl (a : AbsHeapType) : a.Matches a := by
  cases a <;> decide

theorem AbsHeapType.Matches.trans {a b c : AbsHeapType}
    (h : a.Matches b) (k : b.Matches c) : a.Matches c := by
  cases a <;> cases b <;> cases c <;> first | exact h | exact k | contradiction

theorem AbsHeapType.Matches.antisymm {a b : AbsHeapType}
    (h : a.Matches b) (k : b.Matches a) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

/-- Reference matching factors into nullability and the chosen heap relation. -/
def RefType.Matches (heapMatch : HeapType → HeapType → Prop) (a b : RefType) : Prop :=
  (a.nullable = true → b.nullable = true) ∧ heapMatch a.heap b.heap

instance (heapMatch : HeapType → HeapType → Prop) [DecidableRel heapMatch]
    (a b : RefType) : Decidable (a.Matches heapMatch b) := by
  unfold RefType.Matches
  infer_instance

theorem RefType.Matches.refl {heapMatch : HeapType → HeapType → Prop}
    (h : ∀ a, heapMatch a a) (a : RefType) : a.Matches heapMatch a := ⟨id, h _⟩

theorem RefType.Matches.trans {heapMatch : HeapType → HeapType → Prop}
    (trans : ∀ {a b c}, heapMatch a b → heapMatch b c → heapMatch a c)
    {a b c : RefType} (h : a.Matches heapMatch b) (k : b.Matches heapMatch c) :
    a.Matches heapMatch c := ⟨k.1 ∘ h.1, trans h.2 k.2⟩

theorem RefType.Matches.nullable_target {heapMatch : HeapType → HeapType → Prop}
    {a b : RefType} (h : a.Matches heapMatch b) (ha : a.nullable = true) :
    b.nullable = true := h.1 ha

/-- Immutable fields are covariant; mutable fields require matching both ways. -/
def FieldType.Matches (storageMatch : StorageType → StorageType → Prop)
    (a b : FieldType) : Prop :=
  a.mutability = b.mutability ∧ storageMatch a.storage b.storage ∧
    (a.mutability = .var → storageMatch b.storage a.storage)

instance (storageMatch : StorageType → StorageType → Prop) [DecidableRel storageMatch]
    (a b : FieldType) : Decidable (a.Matches storageMatch b) := by
  unfold FieldType.Matches
  infer_instance

theorem FieldType.Matches.mutable_invariant {storageMatch : StorageType → StorageType → Prop}
    {a b : FieldType} (h : a.Matches storageMatch b) (ha : a.mutability = .var) :
    storageMatch a.storage b.storage ∧ storageMatch b.storage a.storage := ⟨h.2.1, h.2.2 ha⟩

theorem FieldType.Matches.refl {storageMatch : StorageType → StorageType → Prop}
    (h : ∀ a, storageMatch a a) (a : FieldType) : a.Matches storageMatch a :=
  ⟨rfl, h _, fun _ => h _⟩

theorem FieldType.Matches.trans {storageMatch : StorageType → StorageType → Prop}
    (trans : ∀ {a b c}, storageMatch a b → storageMatch b c → storageMatch a c)
    {a b c : FieldType} (h : a.Matches storageMatch b) (k : b.Matches storageMatch c) :
    a.Matches storageMatch c := by
  refine ⟨h.1.trans k.1, trans h.2.1 k.2.1, fun ha => ?_⟩
  exact trans (k.2.2 (h.1 ▸ ha)) (h.2.2 ha)

/-- Declarative defaultability, separate from the executable Boolean test. -/
inductive ValType.Defaultable : ValType → Prop where
  | num (t : NumType) : Defaultable (.num t)
  | vec (t : VecType) : Defaultable (.vec t)
  | ref (heap : HeapType) : Defaultable (.ref ⟨true, heap⟩)

theorem ValType.defaultable_eq_true (t : ValType) :
    t.defaultable = true ↔ t.Defaultable := by
  constructor
  · cases t with
    | num t => exact fun _ => .num t
    | vec t => exact fun _ => .vec t
    | ref t =>
      rcases t with ⟨nullable, heap⟩
      cases nullable
      · simp [defaultable]
      · exact fun _ => .ref heap
  · intro h
    cases h <;> rfl

instance (t : ValType) : Decidable t.Defaultable :=
  decidable_of_iff (t.defaultable = true) t.defaultable_eq_true

/-! Boundary examples use kernel evaluation of the executable conditions. -/

example : (MemoryType.mk .i32 ⟨65536, some 65536⟩).Valid := by decide
example : ¬(MemoryType.mk .i32 ⟨65537, none⟩).Valid := by decide
example : ¬(TableType.mk .i32 ⟨2 ^ 32, none⟩ ⟨true, .abstract .func⟩).Valid 0 := by decide
example : ¬(Limits.mk 3 (some 2)).Valid 10 := by decide
example : AbsHeapType.Matches .none .any := by decide
example : ¬AbsHeapType.Matches .nofunc .any := by decide
example : ¬ValType.Defaultable (.ref ⟨false, .abstract .func⟩) := by decide

/-- Recursive field references may point to the current group member. -/
example : RecType.StructurallyValid []
    ⟨[⟨true, [], .struct [⟨.const, .val (.ref ⟨true, .typeIdx ⟨0⟩⟩)⟩]⟩]⟩ := by decide

/-- A type cannot declare itself as its supertype. -/
example : ¬(RecType.mk [⟨false, [⟨0⟩], .struct []⟩]).StructurallyValid [] := by decide

end Silmaril.Wasm
