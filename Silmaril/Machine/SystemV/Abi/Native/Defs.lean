module

public import Silmaril.Machine.SystemV.Abi.Defs

/-! Classification of the richer native C type vocabulary. Record allocation
(including implementation-defined bitfield packing) is explicit target input.
The source member order and types are retained, rather than recovered from a
lowered integer/aggregate encoding. Metadata acceptance is not a layout theorem
for Clang, GCC, or Cerberus.
-/

@[expose] public section
namespace Silmaril.Machine.SystemV.Abi

namespace Native

open Silmaril.Cerberus.NativeTypes

/-- One bit offset for every declared member, including zero-width bitfields.
The flexible member contributes no field or storage bytes. -/
structure RecordLayout where
  size : Nat
  align : Nat
  offsets : List Nat
  deriving DecidableEq, Repr

/-- Record offsets and atomic storage are target implementation data. Providing
these values is an explicit obligation of a frontend/layout certificate. Atomic
objects may require a storage representation different from their value type. -/
structure Target where
  types : Environment
  records : AggregateKind → Nat → Option RecordLayout
  atomics : CType → Option Object := fun _ => none

def vectorObject (element : Scalar) (lanes : Nat) : Except String Object := do
  if lanes == 0 then throw "native vector must have nonzero lanes"
  match element with
  | .boolean | .bitInt .. =>
      throw "extended vector element needs explicit target storage metadata"
  | _ => pure ()
  let layout ← element.layout
  Object.vector (layout.size * lanes)

/-- Classify a native type without erasing vectors, complex values, `_BitInt`,
record member offsets, bitfield widths, or atomic target metadata. -/
def objectOfTypeWithFuel : Nat → Target → CType → Except String Object
  | 0, _, _ => .error "native type classification exhausted recursive tag fuel"
  | fuel + 1, target, type => do
      match type with
      | .void | .function .. => throw "type is not a complete native object"
      | .scalar scalar => Object.scalar scalar
      | .pointer _ => return .pointer
      | .complex component => return complex component
      | .vector element lanes => vectorObject element lanes
      | .qualified _ type => objectOfTypeWithFuel fuel target type
      | .enumeration tag =>
          let some scalar := target.types.enums tag
            | throw "enum needs its resolved implementation scalar"
          match scalar with
          | .floating _ => throw "enum implementation type must be integral"
          | _ => Object.scalar scalar
      | .atomic underlying =>
          let some object := target.atomics underlying
            | throw "atomic object requires explicit target ABI storage metadata"
          unless object.valid do throw "invalid atomic target ABI storage metadata"
          return object
      | .array _ none => throw "incomplete array is not a complete native object"
      | .array element (some count) =>
          let element ← objectOfTypeWithFuel fuel target element
          let size := count * element.size
          if size > 64 then return .memory size element.align
          return aggregate size element.align ((List.range count).map fun index =>
            ⟨index * element.size * 8, element, none⟩)
      | .record kind tag =>
          let some record := target.types.records tag | throw "missing native record definition"
          unless record.kind == kind do throw "record tag kind mismatch"
          let some layout := target.records kind tag | throw "missing resolved native member offsets"
          unless layout.offsets.length == record.members.length do
            throw "record offset count differs from declared member count"
          unless validAlignment layout.align && layout.size % layout.align == 0 do
            throw "invalid native record size/alignment"
          if let some declared := record.alignment then
            unless validAlignment declared && layout.align ≥ declared do
              throw "record layout violates its explicit alignment"
          let mut fields := []
          for (member, offset) in record.members.zip layout.offsets do
            match member with
            | .field _ type declared =>
                let object ← objectOfTypeWithFuel fuel target type
                unless offset % 8 == 0 && offset + 8 * object.size ≤ 8 * layout.size do
                  throw "native record field is outside its byte storage"
                let alignment := max (if record.packed then 1 else object.align) (declared.getD 1)
                unless validAlignment alignment && layout.align ≥ alignment &&
                    offset % (8 * alignment) == 0 do
                  throw "native record field violates its declared alignment"
                if kind == .union && offset != 0 then
                  throw "native union member has nonzero offset"
                fields := fields ++ [⟨offset, object, none⟩]
            | .bitField _ scalar width =>
                let scalarLayout ← scalar.layout
                match scalar with
                | .floating _ => throw "bitfield implementation type must be integral"
                | _ => pure ()
                unless width ≤ scalarLayout.valueBits && offset + width ≤ 8 * layout.size do
                  throw "native bitfield width/offset exceeds its declared storage"
                if kind == .union && offset != 0 then
                  throw "native union bitfield has nonzero offset"
                fields := fields ++ [⟨offset, ← Object.scalar scalar, some width⟩]
          if let some flexible := record.flexible then
            if kind == .union then throw "union cannot have a flexible array member"
            let element ← objectOfTypeWithFuel fuel target flexible
            unless record.packed || layout.align ≥ element.align do
              throw "native record alignment omits its flexible member"
          let object := aggregate layout.size layout.align fields
          unless object.valid do throw "invalid resolved native record classes"
          return object

def objectOfType (target : Target) (type : CType) : Except String Object :=
  objectOfTypeWithFuel 256 target type

end Native
end Silmaril.Machine.SystemV.Abi
