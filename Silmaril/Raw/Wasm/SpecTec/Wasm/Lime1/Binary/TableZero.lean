module

public import Silmaril.Wasm.Lime1.Types

/-! # The Lime1 `call_indirect` table-zero immediate

WebAssembly 1.0 requires a literal zero byte at this position. Lime1 permits
unsigned-u32 LEB encodings of zero, including overlong forms: at most four
continuation bytes `0x80`, followed by `0x00`. The table index is still zero.
The public predicates and recognizer accept native `ByteArray` values; the
inductive grammar uses lists of `UInt8` only as a logical presentation.
This module describes this immediate only, not a complete binary decoder.

See the [pinned profile](https://github.com/WebAssembly/tool-conventions/blob/83e5d715d0c18aee51e2d5ae9434f22d67b6e905/Lime.md).
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Binary

abbrev Byte := UInt8

/-- The unsigned LEB zero grammar, before imposing the u32 length bound. -/
inductive ZeroPayload : List Byte → Prop where
  | stop : ZeroPayload [0]
  | more {bytes} : ZeroPayload bytes → ZeroPayload (128 :: bytes)

/-- Exactly the u32 encodings accepted for Lime1's reserved table-zero operand. -/
def TableZero (bytes : ByteArray) : Prop :=
  ZeroPayload bytes.data.toList ∧ bytes.size ≤ 5

/-- WebAssembly 1.0's reserved operand is a single literal zero byte. -/
def V1TableZero (bytes : ByteArray) : Prop := bytes = ⟨#[0]⟩

theorem ZeroPayload.iff_padding (bytes : List Byte) :
    ZeroPayload bytes ↔ ∃ n : Nat, bytes = List.replicate n 128 ++ [0] := by
  constructor
  · intro h
    induction h with
    | stop => exact ⟨0, rfl⟩
    | more h ih =>
      obtain ⟨n, rfl⟩ := ih
      exact ⟨n + 1, by simp [List.replicate_succ]⟩
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => exact .stop
    | succ n ih => simpa [List.replicate_succ] using ZeroPayload.more ih

/-- The logical grammar agrees with native array padding and a final zero byte. -/
theorem zeroPayload_iff (bytes : ByteArray) :
    ZeroPayload bytes.data.toList ↔
      ∃ n : Nat, bytes = ⟨(Array.replicate n 128).push 0⟩ := by
  simp only [ZeroPayload.iff_padding, ByteArray.ext_iff, ← Array.toList_inj,
    Array.toList_push, Array.toList_replicate]

/-- There are exactly five permitted byte strings, with zero through four pads. -/
theorem tableZero_iff (bytes : ByteArray) :
    TableZero bytes ↔
      ∃ n : Nat, n ≤ 4 ∧ bytes = ⟨(Array.replicate n 128).push 0⟩ := by
  simp only [TableZero, zeroPayload_iff]
  constructor
  · rintro ⟨⟨n, rfl⟩, h⟩
    simp only [ByteArray.size, Array.size_push, Array.size_replicate] at h
    exact ⟨n, by omega, rfl⟩
  · rintro ⟨n, h, rfl⟩
    refine ⟨⟨n, rfl⟩, ?_⟩
    simp only [ByteArray.size, Array.size_push, Array.size_replicate]
    omega

/-- An executable recognizer using native byte-array equality, without list conversion. -/
def tableZero (bytes : ByteArray) : Bool :=
  #[0, 1, 2, 3, 4].any fun n => decide (bytes = ⟨(Array.replicate n 128).push 0⟩)

@[simp] theorem tableZero_eq_true (bytes : ByteArray) :
    tableZero bytes = true ↔ TableZero bytes := by
  have mem (n : Nat) : n ∈ #[0, 1, 2, 3, 4] ↔ n ≤ 4 := by
    simp
    omega
  simp only [tableZero, Array.any_eq_true', mem, decide_eq_true_eq, tableZero_iff]

theorem v1TableZero_tableZero {bytes : ByteArray} (h : V1TableZero bytes) :
    TableZero bytes := by
  subst bytes
  exact ⟨.stop, by decide⟩

theorem tableZero_size {bytes : ByteArray} (h : TableZero bytes) :
    1 ≤ bytes.size ∧ bytes.size ≤ 5 := by
  obtain ⟨n, hn, rfl⟩ := (tableZero_iff bytes).mp h
  simp only [ByteArray.size, Array.size_push, Array.size_replicate]
  omega

/-- The overlong encoding in the profile's published feature test. -/
theorem feature_test : TableZero ⟨#[128, 128, 128, 0]⟩ := by
  exact (tableZero_eq_true _).mp (by decide +kernel)

theorem overlong_not_v1 : ¬ V1TableZero ⟨#[128, 0]⟩ := by
  simp [V1TableZero, ByteArray.ext_iff]

theorem six_bytes_rejected : ¬ TableZero ⟨#[128, 128, 128, 128, 128, 0]⟩ := by
  intro h
  have := h.2
  contradiction

theorem nonzero_table_rejected : ¬ TableZero ⟨#[1]⟩ := by
  rw [← tableZero_eq_true]
  decide +kernel

end Silmaril.Wasm.Lime1.Binary
