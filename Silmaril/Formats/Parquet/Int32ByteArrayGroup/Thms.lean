module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Defs
import Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.Correctness

/-! Same-snapshot selection, exact ordered pairs, and deterministic error order. -/

public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup

/-- Page decoding depends on the column and value limits. File byte and
snapshot admission are handled separately. -/
theorem decoders_congr {left right : Limits}
    (page : left.column = right.column) (valueBytes : left.maxValueBytes = right.maxValueBytes)
    (layout : FlatColumn.Layout) :
    decodeInt32 left layout = decodeInt32 right layout ∧
    decodeByteArray left layout = decodeByteArray right layout :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.decoders_congr page valueBytes layout

theorem openFile_snapshot {limits : Limits} {source : Bytes} {int32 byteArray : Field}
    {checked : Checked int32 byteArray} (opened : openFile limits source int32 byteArray = .ok checked) :
    Snapshot.check (Failure := Unit) limits.snapshot source = .ok checked.snapshot ∧
    checked.snapshot.metadata.schema[checked.int32Binding.leafOrdinal]? = some checked.int32Binding.leaf ∧
    checked.snapshot.metadata.schema[checked.byteArrayBinding.leafOrdinal]? = some checked.byteArrayBinding.leaf :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.openFile_snapshot opened

/-- Two successful column reads necessarily have equal sizes and yield the
complete positional pairing. -/
theorem readGroup_of_columns {int32 byteArray : Field} {checked : Checked int32 byteArray}
    {limits : Limits} {index : Nat} {integers : List (Option Int32)} {bytes : List (Option Bytes)}
    (readInts : checked.readInt32 limits index = .ok integers)
    (readBytes : checked.readByteArray limits index = .ok bytes) :
    integers.length = bytes.length ∧ checked.readGroup limits index = .ok (integers.zip bytes) :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.readGroup_of_columns readInts readBytes

/-- The projections recover both complete slot lists, irrespective of the
page partitions of the two original chunks. -/
theorem readGroup_wire {int32 byteArray : Field} {checked : Checked int32 byteArray}
    {limits : Limits} {index : Nat} {rows : List Row}
    (read : checked.readGroup limits index = .ok rows) : GroupWire checked limits index rows :=
  Proofs.Formats.Parquet.Int32ByteArrayGroup.readGroup_wire read

theorem readGroup_int32_error {int32 byteArray : Field} {checked : Checked int32 byteArray}
    {limits : Limits} {index : Nat} {reason : FlatColumn.Error FlatScan.AdapterError}
    (failed : checked.readInt32 limits index = .error reason) :
    checked.readGroup limits index = .error (.int32 reason) := by
  simp [Checked.readGroup, failed]

theorem readGroup_byteArray_error {int32 byteArray : Field} {checked : Checked int32 byteArray}
    {limits : Limits} {index : Nat} {integers : List (Option Int32)}
    {reason : FlatColumn.Error Plain.ByteArray.File.PageError}
    (earlier : checked.readInt32 limits index = .ok integers)
    (failed : checked.readByteArray limits index = .error reason) :
    checked.readGroup limits index = .error (.byteArray reason) := by
  simp [Checked.readGroup, earlier, failed]

end Silmaril.Formats.Parquet.Int32ByteArrayGroup
