module

public import Silmaril.Machine.SystemV.Abi.Representation.Defs
public import Silmaril.Cerberus.NativeValues.Thms

@[expose] public section
namespace Silmaril.Machine.SystemV.Abi.Representation

open Silmaril.Cerberus
open NativeTypes NativeValues

theorem littleEndian_length (value count : Nat) : (littleEndian value count).length = count := by
  simp only [littleEndian, List.length_map, List.length_range]

/-- Exact byte length is derived from the finite image; semantic storage remains
an additional concrete obligation. No externally supplied encoder is used. -/
theorem representation_encodes_iff (context : Context) (type : CType) (object : Object)
    (value : TypedValue context.values type) (bytes : Bytes) :
    (representation context type object).encodes value bytes ↔
      bytes.length = object.size ∧ Stores context type value.value bytes := by
  constructor
  · rintro ⟨image, stored, rfl⟩
    exact ⟨List.length_ofFn, stored⟩
  · rintro ⟨size, stored⟩
    let image : Image object.size := fun index => bytes[index.val]'(by omega)
    have image_eq : List.ofFn image = bytes := by
      apply List.ext_getElem
      · simpa only [List.length_ofFn] using size.symm
      · intro index firstBound secondBound
        simp only [List.getElem_ofFn, image]
    exact ⟨image, image_eq.symm ▸ stored, image_eq.symm⟩

theorem representation_typed (context : Context) (type : CType) (object : Object)
    (value : (representation context type object).Value) :
    WellFormed context.target.types type ∧ HasType context.values type value.value :=
  value.type_derivation

/-- Changing address resolution cannot change the independent C type derivation.
Whether a particular pointer has native storage is a separate representation fact. -/
theorem Context.values_allocationAddresses (context : Context) (addresses : Nat → Option Nat) :
    ({context with allocationAddresses := addresses}).values = context.values := rfl

theorem Context.values_functionAddresses (context : Context) (addresses : String → Option Nat) :
    ({context with functionAddresses := addresses}).values = context.values := rfl

/-- The atomic checks preserve actual payload alignment when the object base
has its declared alignment. This is natural-number placement, not a no-wrap or
atomic-machine-execution theorem. -/
theorem atomic_payload_aligned {base offset storageAlignment payloadAlignment : Nat}
    (baseAligned : storageAlignment ∣ base)
    (storageAligned : payloadAlignment ∣ storageAlignment)
    (offsetAligned : payloadAlignment ∣ offset) : payloadAlignment ∣ base + offset := by
  obtain ⟨first, base⟩ := storageAligned.trans baseAligned
  obtain ⟨second, offset⟩ := offsetAligned
  exact ⟨first + second, by rw [base, offset, Nat.mul_add]⟩

theorem ScalarStores.of_padding {scalar : Scalar} {value : Value} {first second : Bytes}
    {layout : Layout} (classified : scalar.layout = .ok layout)
    (stored : ScalarStores scalar value first) (sameLength : first.length = second.length)
    (sameValueBits : readBits first 0 (scalarStorageWidth scalar) =
      readBits second 0 (scalarStorageWidth scalar)) :
    ScalarStores scalar value second := by
  obtain ⟨actual, bits, actualLayout, payload, size, valueBits⟩ := stored
  have sameLayout : actual = layout := Except.ok.inj (actualLayout.symm.trans classified)
  subst actual
  exact ⟨layout, bits, classified, payload, sameLength ▸ size, sameValueBits ▸ valueBits⟩

theorem Stores.pointer_address {context : Context} {pointee : CType} {pointer : Pointer}
    {bytes : Bytes} (stored : Stores context (.pointer pointee) (.pointer pointer) bytes) :
    ∃ address, context.address pointer = some address ∧ bytes.length = 8 ∧
      readBits bytes 0 64 = address := by
  cases stored with
  | pointer resolved size payload => exact ⟨_, resolved, size, payload⟩

theorem Stores.structure_fields {context : Context} {tag : Nat} {values : List Value} {bytes : Bytes}
    (stored : Stores context (.record .struct tag) (.structure values) bytes) :
    ∃ record layout, context.target.types.records tag = some record ∧ record.kind = .struct ∧
      context.target.records .struct tag = some layout ∧ bytes.length = layout.size ∧
      FieldsStore context record.members values layout.offsets bytes := by
  cases stored with
  | «structure» registered kind resolved size fields => exact ⟨_, _, registered, kind, resolved, size, fields⟩

theorem Stores.union_active {context : Context} {tag active : Nat} {value : Value} {bytes : Bytes}
    (stored : Stores context (.record .union tag) (.union active value) bytes) :
    ∃ record layout member offset, context.target.types.records tag = some record ∧
      record.kind = .union ∧ context.target.records .union tag = some layout ∧
      record.members[active]? = some member ∧ layout.offsets[active]? = some offset ∧
      bytes.length = layout.size ∧ MemberStores context member value bytes offset := by
  cases stored with
  | union registered kind resolved selected position size memberStored =>
      exact ⟨_, _, _, _, registered, kind, resolved, selected, position, size, memberStored⟩

theorem FieldsStore.head {context : Context} {member : Member} {value : Value} {offset : Nat}
    {members : List Member} {values : List Value} {offsets : List Nat} {bytes : Bytes}
    (stored : FieldsStore context (member :: members) (value :: values) (offset :: offsets) bytes) :
    MemberStores context member value bytes offset ∧ FieldsStore context members values offsets bytes := by
  cases stored with
  | cons head tail => exact ⟨head, tail⟩

theorem Spec.classifier {context : Context} {type : CType} (spec : Spec context type) :
    Native.objectOfType context.target spec.toFfi.type = .ok spec.toFfi.object := spec.classified

theorem Spec.encodes_iff {context : Context} {type : CType} (spec : Spec context type)
    (value : TypedValue context.values type) (bytes : Bytes) :
    spec.toFfi.representation.encodes value bytes ↔
      bytes.length = spec.object.size ∧ Stores context type value.value bytes :=
  representation_encodes_iff context type spec.object value bytes

/-- The actual FFI argument predicate now consumes concrete independently typed
C values and their compositional storage, at real planner-selected locations. -/
theorem Spec.argumentAt_iff {context : Context} {type : CType} (spec : Spec context type)
    (state : Ffi.State) (value : TypedValue context.values type) (argument : Argument) :
    Ffi.ArgumentAt state spec.toFfi value argument ↔
      argument.object = spec.object ∧ ∃ bytes, bytes.length = spec.object.size ∧
        Stores context type value.value bytes ∧
        match argument.stackOffset with
        | none => Ffi.ChunksAt state bytes argument.chunks
        | some offset => Ffi.StoredAt state ((state.machine.core.read .rsp).toNat + 8 + offset) bytes := by
  change (argument.object = spec.object ∧ ∃ bytes,
    (representation context type spec.object).encodes value bytes ∧ _) ↔ _
  simp only [representation_encodes_iff, and_assoc]
  rfl

/-- Canonical FFI representations preserve both type derivations and active
provenance-rich values; matching bytes alone is never used to manufacture either. -/
theorem Spec.encoded_type {context : Context} {type : CType} (spec : Spec context type)
    (value : TypedValue context.values type) {bytes : Bytes}
    (_encoded : spec.toFfi.representation.encodes value bytes) :
    WellFormed context.target.types type ∧ HasType context.values type value.value :=
  value.type_derivation

end Silmaril.Machine.SystemV.Abi.Representation
