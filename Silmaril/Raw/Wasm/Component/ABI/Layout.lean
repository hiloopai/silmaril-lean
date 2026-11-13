module

public import Silmaril.Wasm.Component.Reference.ABI.Layout.Defs

public import Silmaril.Raw.Wasm.Component.WIT
public import Mathlib.Data.Nat.Basic

/-!
# Canonical ABI memory layout

Alignment and element size for resolved value types, with explicit memory32 or
memory64 pointers. Layouts describe one value's representation: the payloads of
dynamic lists and strings live elsewhere. Invalid raw shapes have total layout
operations, but no conformance claim; use WIT well-formedness separately.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

universe u

theorem le_alignTo (n : Nat) (a : Alignment) : n ≤ alignTo n a := by
  cases a <;> simp only [alignTo, Alignment.bytes] <;> omega

theorem alignTo_lt (n : Nat) (a : Alignment) : alignTo n a < n + a.bytes := by
  cases a <;> simp only [alignTo, Alignment.bytes] <;> omega

theorem alignment_dvd_alignTo (n : Nat) (a : Alignment) : a.bytes ∣ alignTo n a :=
  ⟨(n + a.bytes - 1) / a.bytes, Nat.mul_comm ..⟩

theorem alignTo_eq_self {n : Nat} {a : Alignment} (aligned : a.bytes ∣ n) : alignTo n a = n := by
  obtain ⟨k, rfl⟩ := aligned
  cases a <;> simp only [alignTo, Alignment.bytes] <;> omega

theorem Layout.alignment_dvd_size (l : Layout) : l.alignment.bytes ∣ l.size :=
  ⟨l.units, Nat.mul_comm ..⟩

theorem placeField_offset_ge (cursor : Nat) (field : Layout) : cursor ≤ (placeField cursor field).1 :=
  le_alignTo ..

theorem placeField_aligned (cursor : Nat) (field : Layout) :
    field.alignment.bytes ∣ (placeField cursor field).1 := alignment_dvd_alignTo ..

theorem placeField_end_ge (cursor : Nat) (field : Layout) :
    cursor + field.size ≤ (placeField cursor field).2 := Nat.add_le_add_right (le_alignTo ..) _

theorem recordEnd_ge (cursor : Nat) (fields : List Layout) : cursor ≤ recordEnd cursor fields := by
  induction fields generalizing cursor with
  | nil => exact Nat.le_refl _
  | cons f fs ih =>
    exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (placeField_end_ge cursor f) (ih _))

/-- A record's final padding cannot overlap any next field placed after its
unpadded end. -/
theorem record_end_le_size (fields : List Layout) : recordEnd 0 fields ≤ (recordLayout fields).size :=
  le_alignTo ..

variable {Resource : Type u}

/-- Fixed lists occupy consecutive, aligned copies of their element. -/
theorem layout_fixedList_size (p : AddrType) (t : WIT.ClosedType Resource) (n : Nat) :
    (layout p (.fixedList t n)).size = n * (layout p t).size := by
  simp only [layout, Layout.size, Nat.mul_assoc]

theorem layout_aligned (p : AddrType) (t : WIT.ClosedType Resource) :
    (layout p t).alignment.bytes ∣ (layout p t).size := Layout.alignment_dvd_size _

end Silmaril.Wasm.Component.ABI
