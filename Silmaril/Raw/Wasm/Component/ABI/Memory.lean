module

public import Silmaril.Wasm.Component.Reference.ABI.Memory.Defs

public import Silmaril.Raw.Wasm.Component.ABI.Scalar
public import Silmaril.Raw.Wasm.Component.ABI.Layout
public import Silmaril.Raw.Wasm.Component.Wasm.Execution.Memory.Lemmas

/-!
# Canonical integer record buffers

Native `ByteArray` operations encode booleans and integers in little-endian
memory. The low-level scalar helpers allow unaligned access; `storeRecord` and
`loadRecord` impose canonical record alignment and full bounds, including tail
padding. Fields are aligned individually and padding bytes are untouched.

These codecs operate on an already allocated buffer. They do not implement
realloc, ownership, post-return, or an indirect component call. Scalar records
are a shared foundation for indirect parameter/result tuples. Natural offsets
are bounded by the supplied byte array; pointer-width validation belongs to the
calling adapter that supplies an offset.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

open Silmaril.Wasm.Execution

private theorem storage_roundtrip (t : Scalar) (x : BitVec t.width) :
    t.liftBits (x.setWidth (8 * t.byteCount)) = x := by
  cases t <;> dsimp only [Scalar.width] at x
  all_goals simp [Scalar.liftBits, Scalar.width, Scalar.byteCount]
  have hx : x.toNat = 0 ∨ x.toNat = 1 := by
    have bound := x.isLt
    omega
  rcases hx with hx | hx
  · have h : x = 0 := BitVec.eq_of_toNat_eq hx
    subst x
    rfl
  · have h : x = 1 := BitVec.eq_of_toNat_eq hx
    subst x
    rfl

theorem Scalar.load_store (memory after : ByteArray) (start : Nat) (v : ScalarValue)
    (h : v.store memory start = some after) : v.type.load after start = some v := by
  unfold Scalar.load
  rw [Memory.load_store memory after start v.type.byteCount _ h]
  simp only [Option.map_some, storage_roundtrip]

theorem ScalarValue.store_size (memory after : ByteArray) (start : Nat) (v : ScalarValue)
    (h : v.store memory start = some after) : after.size = memory.size :=
  Memory.writeBytes_size memory _ after start h

theorem Scalar.load_store_disjoint (t : Scalar) (memory after : ByteArray)
    (start readStart : Nat) (v : ScalarValue) (h : v.store memory start = some after)
    (disjoint : readStart + t.byteCount ≤ start ∨ start + v.type.byteCount ≤ readStart) :
    t.load after readStart = t.load memory readStart := by
  unfold Scalar.load
  rw [Memory.load_store_disjoint memory after start readStart t.byteCount v.type.byteCount _ h disjoint]

theorem storeFields_size (memory after : ByteArray) (cursor : Nat) (vs : List ScalarValue)
    (h : storeFields memory cursor vs = some after) : after.size = memory.size := by
  induction vs generalizing memory cursor with
  | nil => simp only [storeFields, Option.some.injEq] at h; cases h; rfl
  | cons v vs ih =>
    simp only [storeFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨next, hnext, htail⟩ := h
    exact (ih _ _ htail).trans (v.store_size _ _ _ hnext)

/-- Storing a record suffix cannot alter a scalar entirely before its cursor. -/
theorem load_storeFields_before (t : Scalar) (memory after : ByteArray) (cursor readStart : Nat)
    (vs : List ScalarValue) (h : storeFields memory cursor vs = some after)
    (before : readStart + t.byteCount ≤ cursor) : t.load after readStart = t.load memory readStart := by
  induction vs generalizing memory cursor with
  | nil => simp only [storeFields, Option.some.injEq] at h; cases h; rfl
  | cons v vs ih =>
    simp only [storeFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨next, hnext, htail⟩ := h
    have startBound := le_alignTo cursor v.type.alignment
    have stepBound : readStart + t.byteCount ≤ alignTo cursor v.type.alignment :=
      Nat.le_trans before startBound
    rw [ih _ _ htail (by omega)]
    exact t.load_store_disjoint _ _ _ _ v hnext (.inl stepBound)

theorem loadFields_storeFields (memory after : ByteArray) (cursor : Nat) (vs : List ScalarValue)
    (h : storeFields memory cursor vs = some after) :
    loadFields after cursor (vs.map ScalarValue.type) = some vs := by
  induction vs generalizing memory cursor with
  | nil => rfl
  | cons v vs ih =>
    simp only [storeFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨next, hnext, htail⟩ := h
    have head := load_storeFields_before v.type next after
      (alignTo cursor v.type.alignment + v.type.byteCount)
      (alignTo cursor v.type.alignment) vs htail (Nat.le_refl _)
    rw [Scalar.load_store memory next _ v hnext] at head
    simp only [List.map_cons, loadFields, head, ih _ _ htail]
    rfl

theorem storeRecord_bounds {memory after : ByteArray} {start : Nat} {vs : List ScalarValue}
    (h : storeRecord memory start vs = some after) :
    let l := scalarRecordLayout (vs.map ScalarValue.type)
    start % l.alignment.bytes = 0 ∧ start + l.size ≤ memory.size := by
  dsimp only [storeRecord] at h
  split at h
  · assumption
  · contradiction

theorem storeRecord_size {memory after : ByteArray} {start : Nat} {vs : List ScalarValue}
    (h : storeRecord memory start vs = some after) : after.size = memory.size := by
  dsimp only [storeRecord] at h
  split at h
  · exact storeFields_size memory after start vs h
  · contradiction

/-- The bounds check includes tail padding and is stable because stores retain
memory size. Aligned mixed-width records round-trip after every successful write. -/
theorem loadRecord_storeRecord (memory after : ByteArray) (start : Nat) (vs : List ScalarValue)
    (h : storeRecord memory start vs = some after) :
    loadRecord (vs.map ScalarValue.type) after start = some vs := by
  have bounds := storeRecord_bounds h
  have size := storeRecord_size h
  dsimp only [storeRecord] at h
  dsimp only [loadRecord]
  rw [size]
  split at h
  · simp only [bounds]
    exact loadFields_storeFields memory after start vs h
  · contradiction

theorem layoutTypes_scalars (ts : List Scalar) :
    layoutTypes .i32 (ts.map Scalar.wit) = ts.map (fun t => primitiveLayout .i32 t.primitive) := by
  induction ts with
  | nil => simp only [List.map_nil, layoutTypes]
  | cons t ts ih => simp only [List.map_cons, layoutTypes, Scalar.wit, layout, ih]

/-- Buffer layout is the previously defined canonical WIT tuple layout. -/
theorem scalarRecordLayout_eq_layout (ts : List Scalar) :
    scalarRecordLayout ts = layout .i32 (.tuple (ts.map Scalar.wit)) := by
  simp only [scalarRecordLayout, layout, layoutTypes_scalars]

theorem endFields_ge (cursor : Nat) (ts : List Scalar) : cursor ≤ endFields cursor ts := by
  induction ts generalizing cursor with
  | nil => exact Nat.le_refl _
  | cons t ts ih =>
    have fieldStart := le_alignTo cursor t.alignment
    have tail := ih (alignTo cursor t.alignment + t.byteCount)
    simp only [endFields]
    omega

/-- The suffix beyond the final field is unchanged too, including padding. -/
theorem load_storeFields_after (t : Scalar) (memory after : ByteArray) (cursor readStart : Nat)
    (vs : List ScalarValue) (h : storeFields memory cursor vs = some after)
    (beyond : endFields cursor (vs.map ScalarValue.type) ≤ readStart) :
    t.load after readStart = t.load memory readStart := by
  induction vs generalizing memory cursor with
  | nil => simp only [storeFields, Option.some.injEq] at h; cases h; rfl
  | cons v vs ih =>
    simp only [storeFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨next, hnext, htail⟩ := h
    simp only [List.map_cons, endFields] at beyond
    have tailStart := endFields_ge (alignTo cursor v.type.alignment + v.type.byteCount)
      (vs.map ScalarValue.type)
    rw [ih _ _ htail beyond]
    exact t.load_store_disjoint _ _ _ _ v hnext (.inr (by omega))

end Silmaril.Wasm.Component.ABI
