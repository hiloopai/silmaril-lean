module

public import Silmaril.Cerberus.Ctype.Defs

/-! Native LP64 type vocabulary. This deliberately distinguishes the native
AMD64 layouts from the imported Cerberus consumer's eight-byte floating-layout
shortcuts. Named records permit recursive pointer types without recursively
embedding their definitions. A type declaration is not an object layout proof.
-/

@[expose] public section
namespace Silmaril.Cerberus.NativeTypes

inductive Signedness where
  | signed | unsigned
  deriving DecidableEq, BEq, Repr

inductive IntegerKind where
  | char | short | int | long | longLong | int128
  deriving DecidableEq, BEq, Repr

inductive Floating where
  | binary16 | bfloat16 | binary32 | binary64 | x87 | binary128
  | decimal32 | decimal64 | decimal128
  deriving DecidableEq, BEq, Repr

inductive Scalar where
  | boolean
  | integer (kind : IntegerKind) (signedness : Signedness)
  | bitInt (precision : Nat) (signedness : Signedness)
  | floating (format : Floating)
  deriving DecidableEq, BEq, Repr

structure Layout where
  size : Nat
  align : Nat
  /-- Bits that carry the value; padding bits remain separate. -/
  valueBits : Nat
  deriving DecidableEq, BEq, Repr

def IntegerKind.bytes : IntegerKind → Nat
  | .char => 1 | .short => 2 | .int => 4
  | .long | .longLong => 8 | .int128 => 16

def Floating.layout : Floating → Layout
  | .binary16 | .bfloat16 => ⟨2, 2, 16⟩
  | .binary32 | .decimal32 => ⟨4, 4, 32⟩
  | .binary64 | .decimal64 => ⟨8, 8, 64⟩
  | .x87 => ⟨16, 16, 80⟩
  | .binary128 | .decimal128 => ⟨16, 16, 128⟩

/-- `_BitInt` sizes use the smallest standard integer through 64 bits and
64-bit chunks above that, unlike the 16-byte alignment of `__int128`. -/
def bitIntLayout (precision : Nat) : Layout :=
  if precision ≤ 8 then ⟨1, 1, precision⟩
  else if precision ≤ 16 then ⟨2, 2, precision⟩
  else if precision ≤ 32 then ⟨4, 4, precision⟩
  else ⟨8 * ((precision + 63) / 64), 8, precision⟩

def Scalar.layout : Scalar → Except String Layout
  | .boolean => .ok ⟨1, 1, 1⟩
  | .integer kind _ => .ok ⟨kind.bytes, kind.bytes, 8 * kind.bytes⟩
  | .floating format => .ok format.layout
  | .bitInt precision signedness =>
      if precision = 0 || (signedness == .signed && precision = 1) then
        .error "invalid _BitInt precision"
      else .ok (bitIntLayout precision)

inductive AggregateKind where
  | struct | union
  deriving DecidableEq, BEq, Repr

inductive CType where
  | void
  | scalar (type : Scalar)
  | pointer (pointee : CType)
  | array (element : CType) (count : Option Nat)
  | record (kind : AggregateKind) (tag : Nat)
  | enumeration (tag : Nat)
  | complex (component : Floating)
  | vector (element : Scalar) (lanes : Nat)
  | atomic (type : CType)
  | qualified (qualifiers : Silmaril.Cerberus.Qualifiers) (type : CType)
  | function (result : CType) (parameters : List CType) (variadic : Bool)
  deriving Repr

inductive Member where
  | field (name : String) (type : CType) (alignment : Option Nat := none)
  | bitField (name : Option String) (type : Scalar) (width : Nat)
  deriving Repr

structure Record where
  kind : AggregateKind
  members : List Member
  packed : Bool := false
  alignment : Option Nat := none
  /-- The flexible member contributes alignment, not storage size. -/
  flexible : Option CType := none
  deriving Repr

structure Environment where
  records : Nat → Option Record
  enums : Nat → Option Scalar

/-- Native pointers retain semantic identity separately from their ABI address.
A representation context must connect allocations/offsets to machine addresses. -/
inductive Pointer where
  | null
  | object (allocation : Nat) (offset : Int)
  | function (symbol : String)
  deriving DecidableEq, BEq, Repr

/-- Little-endian object storage, including padding. IEEE/x87 bits are storage
representations here; floating arithmetic requires its own semantic operation. -/
abbrev Bytes := List UInt8

structure Representation (type : CType) where
  layout : Layout
  /-- The logical value space need not erase provenance or union membership. -/
  Value : Type
  encodes : Value → Bytes → Prop
  exactSize : ∀ value bytes, encodes value bytes → bytes.length = layout.size

/-- Value equality, rather than byte equality, accounts for unspecified padding. -/
def Representation.Functional {type : CType} (representation : Representation type) : Prop :=
  ∀ first second bytes, representation.encodes first bytes →
    representation.encodes second bytes → first = second

end Silmaril.Cerberus.NativeTypes
