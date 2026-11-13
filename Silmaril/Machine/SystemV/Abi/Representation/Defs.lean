module

public import Silmaril.Cerberus.NativeValues.Defs
public import Silmaril.Machine.SystemV.Abi.Ffi.Defs

/-! Concrete native C object representations consumed by the existing typed FFI.
The logical carrier is `NativeValues.TypedValue`; it never becomes raw storage.
Padding is unconstrained and pointer identities/active union members are retained.
Target layouts and addresses remain explicit implementation inputs. -/

@[expose] public section
namespace Silmaril.Machine.SystemV.Abi.Representation

open Silmaril.Cerberus
open Silmaril.Cerberus.NativeTypes
open Silmaril.Cerberus.NativeValues

structure Context where
  target : Native.Target
  allocations : Nat → Option Allocation := fun _ => none
  functions : String → Option CType := fun _ => none
  allocationAddresses : Nat → Option Nat := fun _ => none
  functionAddresses : String → Option Nat := fun _ => none
  /-- Byte offset of the non-atomic value representation inside explicit atomic
  target storage. Lock/version/control bytes outside this payload stay free. -/
  atomicOffsets : CType → Option Nat := fun _ => none

def Context.values (context : Context) : NativeValues.Environment :=
  ⟨context.target.types, context.allocations, context.functions⟩

def Context.address (context : Context) : Pointer → Option Nat
  | .null => some 0
  | .object identity offset => do
      let base ← context.allocationAddresses identity
      let address := (base : Int) + offset
      if 0 ≤ address ∧ address < 2 ^ 64 then some address.toNat else none
  | .function symbol => do
      let address ← context.functionAddresses symbol
      if address < 2 ^ 64 then some address else none

def littleEndian (value count : Nat) : Bytes :=
  (List.range count).map fun index => UInt8.ofNat (value / 2 ^ (8 * index))

def readNat : Bytes → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * readNat rest

def readBits (bytes : Bytes) (offset width : Nat) : Nat :=
  (readNat bytes / 2 ^ offset) % 2 ^ width

def integerBits (value : Int) (width : Nat) : Nat :=
  (value % (2 ^ width : Int)).toNat

/-- Semantic scalar payload bits. Range/type validity is supplied independently
by `TypedValue`; this function alone is not a C typing judgement. -/
def scalarBits : Scalar → Value → Option Nat
  | .boolean, .boolean value => some (if value then 1 else 0)
  | .integer kind _, .integer value => some (integerBits value (8 * kind.bytes))
  | .bitInt precision _, .integer value => some (integerBits value precision)
  | .floating _, .floating bits => some bits
  | _, _ => none

/-- The native ABI requires a normalized `_Bool` byte, including zero bits 1–7.
Other scalar padding, including x87 and `_BitInt` padding, remains free. -/
def scalarStorageWidth : Scalar → Nat
  | .boolean => 8
  | scalar => ScalarWidth scalar

def ScalarStores (scalar : Scalar) (value : Value) (bytes : Bytes) : Prop :=
  ∃ layout bits, scalar.layout = .ok layout ∧ scalarBits scalar value = some bits ∧
    bytes.length = layout.size ∧ readBits bytes 0 (scalarStorageWidth scalar) = bits

def slice (bytes : Bytes) (offset count : Nat) : Bytes := (bytes.drop offset).take count

def BitFieldStores : Option String → Scalar → Nat → Value → Bytes → Nat → Prop
  | none, _, _, .padding, _, _ => True
  | some _, .boolean, 1, .boolean value, bytes, offset =>
      readBits bytes offset 1 = if value then 1 else 0
  | some _, .integer _ _, width, .integer value, bytes, offset =>
      readBits bytes offset width = integerBits value width
  | some _, .bitInt _ _, width, .integer value, bytes, offset =>
      readBits bytes offset width = integerBits value width
  | _, _, _, _, _, _ => False


mutual
  /-- Compositional value storage. Record/union rules use resolved source member
  positions; they do not infer membership or pointer identity by decoding bytes.
  This relation is paired with independent typing in `Encoding` below. -/
  inductive Stores (context : Context) : CType → Value → Bytes → Prop where
    | scalar {scalar : Scalar} {value : Value} {bytes : Bytes}
        (stored : ScalarStores scalar value bytes) :
        Stores context (.scalar scalar) value bytes
    | pointer {pointer : Pointer} {address : Nat} {bytes : Bytes} {pointee : CType}
        (resolved : context.address pointer = some address)
        (size : bytes.length = 8) (stored : readBits bytes 0 64 = address) :
        Stores context (.pointer pointee) (.pointer pointer) bytes
    | array {element : CType} {object : Object} {values : List Value} {count : Nat} {bytes : Bytes}
        (classified : Native.objectOfType context.target element = .ok object)
        (counted : values.length = count) (size : bytes.length = count * object.size)
        (elements : ∀ index (bound : index < count),
          Stores context element (values[index]'(by omega))
            (slice bytes (index * object.size) object.size)) :
        Stores context (.array element (some count)) (.array values) bytes
    | structure {tag : Nat} {record : Record} {layout : Native.RecordLayout}
        {bytes : Bytes} {values : List Value}
        (registered : context.target.types.records tag = some record)
        (kind : record.kind = .struct)
        (resolved : context.target.records .struct tag = some layout)
        (size : bytes.length = layout.size)
        (fields : FieldsStore context record.members values layout.offsets bytes) :
        Stores context (.record .struct tag) (.structure values) bytes
    | union {tag active offset : Nat} {record : Record} {layout : Native.RecordLayout}
        {member : Member} {bytes : Bytes} {value : Value}
        (registered : context.target.types.records tag = some record)
        (kind : record.kind = .union)
        (resolved : context.target.records .union tag = some layout)
        (selected : record.members[active]? = some member)
        (position : layout.offsets[active]? = some offset)
        (size : bytes.length = layout.size)
        (stored : MemberStores context member value bytes offset) :
        Stores context (.record .union tag) (.union active value) bytes
    | enumeration {tag : Nat} {scalar : Scalar} {value : Value} {bytes : Bytes}
        (registered : context.target.types.enums tag = some scalar)
        (stored : ScalarStores scalar value bytes) :
        Stores context (.enumeration tag) (.enumeration value) bytes
    | complex {format : Floating} {bytes : Bytes} {real imaginary : Value}
        (size : bytes.length = 2 * format.layout.size)
        (realStored : ScalarStores (.floating format) real
          (slice bytes 0 format.layout.size))
        (imaginaryStored : ScalarStores (.floating format) imaginary
          (slice bytes format.layout.size format.layout.size)) :
        Stores context (.complex format) (.complex real imaginary) bytes
    | vector {scalar : Scalar} {scalarLayout : Layout} {values : List Value}
        {lanes : Nat} {bytes : Bytes} (classified : scalar.layout = .ok scalarLayout)
        (counted : values.length = lanes) (size : bytes.length = lanes * scalarLayout.size)
        (elements : ∀ index (bound : index < lanes),
          ScalarStores scalar (values[index]'(by omega))
            (slice bytes (index * scalarLayout.size) scalarLayout.size)) :
        Stores context (.vector scalar lanes) (.vector values) bytes
    | atomic {type : CType} {object storage : Object} {offset : Nat} {bytes : Bytes} {value : Value}
        (classified : Native.objectOfType context.target type = .ok object)
        (resolved : context.target.atomics type = some storage)
        (position : context.atomicOffsets type = some offset)
        (fits : offset + object.size ≤ storage.size)
        (size : bytes.length = storage.size)
        (stored : Stores context type value (slice bytes offset object.size)) :
        Stores context (.atomic type) (.atomic value) bytes
    | qualified {type : CType} {value : Value} {bytes : Bytes}
        {qualifiers : Silmaril.Cerberus.Qualifiers} (stored : Stores context type value bytes) :
        Stores context (.qualified qualifiers type) value bytes
  inductive MemberStores (context : Context) : Member → Value → Bytes → Nat → Prop where
    | field {type : CType} {object : Object} {offset : Nat} {bytes : Bytes} {value : Value}
        {name : String} {declared : Option Nat}
        (classified : Native.objectOfType context.target type = .ok object)
        (byteAligned : offset % 8 = 0) (fits : offset / 8 + object.size ≤ bytes.length)
        (stored : Stores context type value (slice bytes (offset / 8) object.size)) :
        MemberStores context (.field name type declared) value bytes offset
    | bitField {offset width : Nat} {bytes : Bytes} {fieldName : Option String}
        {scalar : Scalar} {value : Value} (fits : offset + width ≤ 8 * bytes.length)
        (stored : BitFieldStores fieldName scalar width value bytes offset) :
        MemberStores context (.bitField fieldName scalar width) value bytes offset
  inductive FieldsStore (context : Context) : List Member → List Value → List Nat → Bytes → Prop where
    | nil {bytes : Bytes} : FieldsStore context [] [] [] bytes
    | cons {member : Member} {value : Value} {bytes : Bytes} {offset : Nat}
        {members : List Member} {values : List Value} {offsets : List Nat}
        (head : MemberStores context member value bytes offset)
        (tail : FieldsStore context members values offsets bytes) :
        FieldsStore context (member :: members) (value :: values) (offset :: offsets) bytes
end

/-- Number of potentially significant value bits. Union activity remains in the
value; its layout reserves the maximum member payload. This is not a bit-position
map and does not reinterpret floating bits or pointer representations. -/
def valueBitsWithFuel : Nat → NativeTypes.Environment → CType → Nat
  | 0, _, _ => 0
  | fuel + 1, types, type =>
      match type with
      | .void | .function .. => 0
      | .scalar scalar => ScalarWidth scalar
      | .pointer _ => 64
      | .array element count => count.getD 0 * valueBitsWithFuel fuel types element
      | .complex format => 2 * format.layout.valueBits
      | .vector scalar lanes => lanes * ScalarWidth scalar
      | .enumeration tag => ((types.enums tag).map ScalarWidth).getD 0
      | .atomic underlying | .qualified _ underlying => valueBitsWithFuel fuel types underlying
      | .record kind tag =>
          match types.records tag with
          | none => 0
          | some record =>
              let bits := record.members.map fun member =>
                match member with
                | .field _ type _ => valueBitsWithFuel fuel types type
                | .bitField none _ _ => 0
                | .bitField (some _) _ width => width
              match kind with
              | .struct => bits.foldl (· + ·) 0
              | .union => bits.foldl max 0

def valueBits (types : NativeTypes.Environment) (type : CType) : Nat :=
  valueBitsWithFuel 256 types type

def separated (ranges : List (Nat × Nat)) : Bool :=
  match ranges with
  | [] => true
  | (start, size) :: rest =>
      rest.all (fun (other, width) => size == 0 || width == 0 ||
        start + size ≤ other || other + width ≤ start) && separated rest

/-- Additional concrete representation checks: complete nonempty arrays, atomic
payload placement, recursive storage support and nonoverlapping struct fields.
The existing classifier independently validates ABI layout/classes. -/
def readyWithFuel : Nat → Context → CType → Except String Unit
  | 0, _, _ => .error "native representation exhausted recursive tag fuel"
  | fuel + 1, context, type => do
      match type with
      | .void | .function .. => throw "type has no complete native object representation"
      | .scalar scalar => let _ ← scalar.layout; return ()
      | .pointer _ | .complex _ | .vector .. | .enumeration _ => return ()
      | .array _ none => throw "incomplete array has no by-value representation"
      | .array element (some count) =>
          if count == 0 then throw "zero-length array has no standard C value"
          readyWithFuel fuel context element
      | .qualified _ underlying => readyWithFuel fuel context underlying
      | .atomic underlying =>
          let object ← Native.objectOfType context.target underlying
          let some storage := context.target.atomics underlying
            | throw "atomic representation needs target storage metadata"
          let some offset := context.atomicOffsets underlying
            | throw "atomic representation needs a payload offset"
          unless offset + object.size ≤ storage.size && object.align != 0 &&
              storage.align % object.align == 0 && offset % object.align == 0 do
            throw "invalid atomic payload placement"
          readyWithFuel fuel context underlying
      | .record kind tag =>
          let some record := context.target.types.records tag
            | throw "missing native representation record definition"
          let some layout := context.target.records kind tag
            | throw "missing native representation record layout"
          unless layout.offsets.length == record.members.length do
            throw "native representation member/offset count mismatch"
          let mut ranges := []
          for (member, offset) in record.members.zip layout.offsets do
            match member with
            | .field _ type _ =>
                let object ← Native.objectOfType context.target type
                readyWithFuel fuel context type
                ranges := ranges ++ [(offset, 8 * object.size)]
            | .bitField _ _ width => ranges := ranges ++ [(offset, width)]
          if kind == .struct && !separated ranges then
            throw "native struct representation has overlapping member storage"
          return ()

def ready (context : Context) (type : CType) : Except String Unit :=
  readyWithFuel 256 context type

/-- A finite byte image fixes its length by construction. The storage predicate
constrains actual scalar/field bits; all remaining padding stays arbitrary. -/
abbrev Image (size : Nat) := Fin size → UInt8

def representation (context : Context) (type : CType) (object : Object) :
    NativeTypes.Representation type where
  layout := ⟨object.size, object.align, valueBits context.target.types type⟩
  Value := TypedValue context.values type
  encodes value bytes := ∃ image : Image object.size,
    Stores context type value.value (List.ofFn image) ∧ bytes = List.ofFn image
  exactSize := by
    intro value bytes encoded
    obtain ⟨image, _, rfl⟩ := encoded
    exact List.length_ofFn

/-- A successful result contains actual classifier/checker equations. It never
accepts an externally supplied Representation or a preassembled FFI object. -/
structure Spec (context : Context) (type : CType) where
  object : Object
  classified : Native.objectOfType context.target type = .ok object
  valid : object.valid = true
  ready : ready context type = .ok ()
  valueBitsFit : valueBits context.target.types type ≤ 8 * object.size

def Spec.toFfi {context : Context} {type : CType} (spec : Spec context type) : Ffi.ObjectSpec where
  type := type
  object := spec.object
  representation := representation context type spec.object
  size := rfl
  alignment := rfl
  valid := spec.valid

def ofType (context : Context) (type : CType) : Except String (Spec context type) := do
  match classified : Native.objectOfType context.target type with
  | .error error => throw error
  | .ok object =>
      if valid : object.valid = true then
        match prepared : ready context type with
        | .error error => throw error
        | .ok () =>
            if fits : valueBits context.target.types type ≤ 8 * object.size then
              return ⟨object, classified, valid, prepared, fits⟩
            else throw "native value payload exceeds its object storage"
      else throw "invalid classified native representation object"

end Silmaril.Machine.SystemV.Abi.Representation
