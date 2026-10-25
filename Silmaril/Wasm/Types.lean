module

public import Mathlib.Data.Fin.Basic

@[expose] public section

/-! # WebAssembly Core 3.0 source types

The source grammar is separate from validation and the administrative types used
during execution. In particular, recursive groups contain type indices; they do
not recursively expand their own definitions.

See the [Core type grammar](https://webassembly.github.io/spec/core/syntax/types.html).
-/

namespace Silmaril.Wasm

inductive IndexKind where
  | type_ | func | table | memory | global | local | label | elem | data | tag | field
  deriving DecidableEq, Repr

/-- Distinct index spaces, each with the specification's unsigned 32-bit range. -/
structure Idx (kind : IndexKind) where
  value : Fin (2 ^ 32)
  deriving DecidableEq, Repr

abbrev TypeIdx := Idx .type_
abbrev FuncIdx := Idx .func
abbrev TableIdx := Idx .table
abbrev MemIdx := Idx .memory
abbrev GlobalIdx := Idx .global
abbrev LocalIdx := Idx .local
abbrev LabelIdx := Idx .label
abbrev ElemIdx := Idx .elem
abbrev DataIdx := Idx .data
abbrev TagIdx := Idx .tag
abbrev FieldIdx := Idx .field

namespace Idx

variable {kind : IndexKind}

def toNat (i : Idx kind) : Nat := i.value.val

/-- Reject an out-of-range index rather than truncating it. -/
def ofNat? (n : Nat) : Option (Idx kind) :=
  if h : n < 2 ^ 32 then some ⟨⟨n, h⟩⟩ else none

theorem toNat_injective : Function.Injective (toNat (kind := kind)) := by
  rintro ⟨a⟩ ⟨b⟩ h
  exact congrArg Idx.mk (Fin.ext h)

@[simp] theorem ofNat?_toNat (i : Idx kind) : ofNat? i.toNat = some i := by
  cases i
  simp [ofNat?, toNat]

theorem ofNat?_eq_some_iff (n : Nat) (i : Idx kind) :
    ofNat? n = some i ↔ n = i.toNat := by
  constructor
  · unfold ofNat?
    split
    · intro h
      cases Option.some.inj h
      rfl
    · simp
  · rintro rfl
    exact ofNat?_toNat i

end Idx

inductive IntType where
  | i32 | i64
  deriving DecidableEq, Repr

inductive FloatType where
  | f32 | f64
  deriving DecidableEq, Repr

inductive NumType where
  | int (type : IntType)
  | float (type : FloatType)
  deriving DecidableEq, Repr

inductive VecType where
  | v128
  deriving DecidableEq, Repr

def IntType.width : IntType → Nat
  | .i32 => 32
  | .i64 => 64

def FloatType.width : FloatType → Nat
  | .f32 => 32
  | .f64 => 64

def NumType.width : NumType → Nat
  | .int t => t.width
  | .float t => t.width

@[simp] theorem IntType.width_pos (t : IntType) : 0 < t.width := by cases t <;> decide
@[simp] theorem FloatType.width_pos (t : FloatType) : 0 < t.width := by cases t <;> decide

inductive AddrType where
  | i32 | i64
  deriving DecidableEq, Repr

def AddrType.intType : AddrType → IntType
  | .i32 => .i32
  | .i64 => .i64

inductive AbsHeapType where
  | any | eq | i31 | struct | array | none
  | func | nofunc | exn | noexn | extern | noextern
  deriving DecidableEq, Repr

inductive HeapType where
  | abstract (type : AbsHeapType)
  | typeIdx (index : TypeIdx)
  deriving DecidableEq, Repr

structure RefType where
  nullable : Bool
  heap : HeapType
  deriving DecidableEq, Repr

inductive ValType where
  | num (type : NumType)
  | vec (type : VecType)
  | ref (type : RefType)
  deriving DecidableEq, Repr

abbrev ResultType := List ValType

def ValType.i32 : ValType := .num (.int .i32)
def ValType.i64 : ValType := .num (.int .i64)
def ValType.f32 : ValType := .num (.float .f32)
def ValType.f64 : ValType := .num (.float .f64)
def ValType.v128 : ValType := .vec .v128

/-- A value type admits an implicit default initializer exactly in these cases. -/
def ValType.defaultable : ValType → Bool
  | .num _ | .vec _ => true
  | .ref r => r.nullable

inductive PackType where
  | i8 | i16
  deriving DecidableEq, Repr

def PackType.width : PackType → Nat
  | .i8 => 8
  | .i16 => 16

inductive StorageType where
  | val (type : ValType)
  | packed (type : PackType)
  deriving DecidableEq, Repr

def StorageType.unpacked : StorageType → ValType
  | .val t => t
  | .packed _ => .i32

inductive Mutability where
  | const | var
  deriving DecidableEq, Repr

structure FieldType where
  mutability : Mutability
  storage : StorageType
  deriving DecidableEq, Repr

structure FuncType where
  params : ResultType
  results : ResultType
  deriving DecidableEq, Repr

inductive CompositeType where
  | func (type : FuncType)
  | struct (fields : List FieldType)
  | array (field : FieldType)
  deriving DecidableEq, Repr

structure SubType where
  final_ : Bool
  supertypes : List TypeIdx
  body : CompositeType
  deriving DecidableEq, Repr

structure RecType where
  types : List SubType
  deriving DecidableEq, Repr

inductive BlockType where
  | empty
  | value (type : ValType)
  | typeIdx (index : TypeIdx)
  deriving DecidableEq, Repr

/-- Limits are syntax; their ordering and address-space bound are validation conditions. -/
structure Limits where
  min : Fin (2 ^ 64)
  max : Option (Fin (2 ^ 64))
  deriving DecidableEq, Repr

structure MemoryType where
  address : AddrType
  limits : Limits
  deriving DecidableEq, Repr

structure TableType where
  address : AddrType
  limits : Limits
  element : RefType
  deriving DecidableEq, Repr

structure GlobalType where
  mutability : Mutability
  value : ValType
  deriving DecidableEq, Repr

abbrev TagType := TypeIdx

inductive ExternType where
  | tag (type : TagType)
  | global (type : GlobalType)
  | memory (type : MemoryType)
  | table (type : TableType)
  | func (type : TypeIdx)
  deriving DecidableEq, Repr

end Silmaril.Wasm
