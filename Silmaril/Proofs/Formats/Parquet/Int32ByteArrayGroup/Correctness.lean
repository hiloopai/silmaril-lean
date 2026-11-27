module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Defs
import all Silmaril.Formats.Parquet.Int32ByteArrayGroup.Defs
import Silmaril.Formats.Parquet.FlatColumn.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Int32ByteArrayGroup

private theorem bind_ok {ε α β : Type} {input : Except ε α} {f : α → Except ε β} {out : β}
    (success : (input >>= f) = .ok out) : ∃ a, input = .ok a ∧ f a = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => exact ⟨a, rfl, success⟩

private theorem mapError_ok {ε δ α : Type} {input : Except ε α} {f : ε → δ} {out : α}
    (success : input.mapError f = .ok out) : input = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => cases success; rfl

theorem decoders_congr {left right : Limits}
    (page : left.column = right.column) (valueBytes : left.maxValueBytes = right.maxValueBytes)
    (layout : FlatColumn.Layout) :
    decodeInt32 left layout = decodeInt32 right layout ∧
    decodeByteArray left layout = decodeByteArray right layout := by
  have same : left.byteArray = right.byteArray := by simp [Limits.byteArray, page, valueBytes]
  simp [decodeInt32, decodeByteArray, same]

theorem openFile_snapshot {limits : Limits} {source : Bytes} {int32 byteArray : Field}
    {checked : Checked int32 byteArray} (opened : openFile limits source int32 byteArray = .ok checked) :
    Snapshot.check (Failure := Unit) limits.snapshot source = .ok checked.snapshot ∧
    checked.snapshot.metadata.schema[checked.int32Binding.leafOrdinal]? = some checked.int32Binding.leaf ∧
    checked.snapshot.metadata.schema[checked.byteArrayBinding.leafOrdinal]? = some checked.byteArrayBinding.leaf := by
  unfold openFile at opened
  split at opened <;> try contradiction
  split at opened <;> try contradiction
  obtain ⟨_, checkedSnapshot, opened⟩ := bind_ok opened
  obtain ⟨left, _, opened⟩ := bind_ok opened
  obtain ⟨right, _, opened⟩ := bind_ok opened
  cases opened
  exact ⟨mapError_ok checkedSnapshot, (FlatColumn.binding_leaf left).1, (FlatColumn.binding_leaf right).1⟩

private theorem column_group {snapshot : Snapshot.Checked} {selection : FlatColumn.Selection}
    {α ε : Type} {binding : FlatColumn.Binding snapshot selection} {limits : FlatColumn.Limits}
    {decode : FlatColumn.DecodePage α ε} {index : Nat} {group : Footer.RowGroup} {slots : List (Option α)}
    (wire : FlatColumn.ColumnWire binding limits decode index group slots) :
    snapshot.groupAt index = some group ∧ slots.length = group.numRows.toNat := by
  obtain ⟨_, _, _, _, selected, _, _, _, _, _, _, _, _, _, _, count⟩ := wire
  exact ⟨selected, count⟩

private theorem columns_wire {int32 byteArray : Field} {checked : Checked int32 byteArray}
    {limits : Limits} {index : Nat} {integers : List (Option Int32)} {bytes : List (Option Bytes)}
    (readInts : checked.readInt32 limits index = .ok integers)
    (readBytes : checked.readByteArray limits index = .ok bytes) :
    ∃ group,
      FlatColumn.ColumnWire checked.int32Binding limits.column (decodeInt32 limits int32.layout) index group integers ∧
      FlatColumn.ColumnWire checked.byteArrayBinding limits.column (decodeByteArray limits byteArray.layout) index group bytes ∧
      integers.length = group.numRows.toNat ∧ bytes.length = group.numRows.toNat := by
  obtain ⟨intGroup, intWire⟩ := FlatColumn.readColumn_wire readInts
  obtain ⟨byteGroup, byteWire⟩ := FlatColumn.readColumn_wire readBytes
  obtain ⟨intAt, intCount⟩ := column_group intWire
  obtain ⟨byteAt, byteCount⟩ := column_group byteWire
  have same : byteGroup = intGroup := Option.some.inj (byteAt.symm.trans intAt)
  rw [same] at byteWire byteCount
  exact ⟨intGroup, intWire, byteWire, intCount, byteCount⟩

theorem readGroup_of_columns {int32 byteArray : Field} {checked : Checked int32 byteArray}
    {limits : Limits} {index : Nat} {integers : List (Option Int32)} {bytes : List (Option Bytes)}
    (readInts : checked.readInt32 limits index = .ok integers)
    (readBytes : checked.readByteArray limits index = .ok bytes) :
    integers.length = bytes.length ∧ checked.readGroup limits index = .ok (integers.zip bytes) := by
  obtain ⟨_, _, _, intCount, byteCount⟩ := columns_wire readInts readBytes
  have equal := intCount.trans byteCount.symm
  exact ⟨equal, by simp [Checked.readGroup, readInts, readBytes, equal]⟩

theorem readGroup_wire {int32 byteArray : Field} {checked : Checked int32 byteArray}
    {limits : Limits} {index : Nat} {rows : List Row}
    (read : checked.readGroup limits index = .ok rows) : GroupWire checked limits index rows := by
  unfold Checked.readGroup at read
  split at read <;> try contradiction
  rename_i integers readInts
  split at read <;> try contradiction
  rename_i bytes readBytes
  obtain ⟨group, intWire, byteWire, intCount, byteCount⟩ := columns_wire readInts readBytes
  have equal := intCount.trans byteCount.symm
  simp only [equal, ite_true, Except.ok.injEq] at read
  subst rows
  have count : (integers.zip bytes).length = group.numRows.toNat := by
    rw [List.length_zip, intCount, byteCount, Nat.min_self]
  exact ⟨group, integers, bytes, intWire, byteWire, readInts, readBytes, equal, count, rfl, List.unzip_zip equal⟩

end Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup
