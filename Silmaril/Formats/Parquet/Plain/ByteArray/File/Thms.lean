module

public import Silmaril.Formats.Parquet.Plain.ByteArray.File.Defs
import Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.File.Wire
import Silmaril.Formats.Parquet.Reader.Thms

/-! Checked source and leaf selection, ordered original bytes, and complete
batches up to the first indexed failure. -/

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.File

/-- Opening binds the named physical leaf at the original serialized ordinal. -/
theorem openFile_wire {limits : Limits} {source : Bytes} {name : String} {layout : FlatColumn.Layout}
    {checked : Checked name layout} (opened : openFile limits source name layout = .ok checked) :
    Snapshot.check (Failure := Unit) limits.snapshot source = .ok checked.snapshot ∧
    source.length ≤ limits.maxFileBytes ∧ checked.snapshot.metadata.numRows.toNat ≤ limits.maxFileRows ∧
    checked.snapshot.metadata.schema[checked.binding.leafOrdinal]? = some checked.binding.leaf ∧
    checked.binding.leaf.name = name ∧ checked.binding.leaf.physicalType = some .byteArray ∧
    checked.binding.leaf.repetition = some layout.repetition :=
  Proofs.Formats.Parquet.Plain.ByteArray.File.openFile_wire opened

/-- The BYTE_ARRAY callback retains the codec selected by the checked chunk
and uses the original page parameters and body. -/
theorem decodePage_wire {limits : Limits} {layout : FlatColumn.Layout}
    {leaf : Footer.SchemaElement} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {frame : Page.Frame} {slots : List (Option Bytes)}
    (decoded : decodePage limits layout leaf metadata frame.value (FlatColumn.frameBody source frame) = .ok slots) :
    PageWire limits layout metadata source frame slots :=
  Proofs.Formats.Parquet.Plain.ByteArray.File.decodePage_wire decoded

/-- The selected chunk's exact original frames yield one ordered slot list per
frame, with the prepared mask, complete PLAIN suffix, and declared row count. -/
theorem readGroup_wire {name : String} {layout : FlatColumn.Layout} {checked : Checked name layout}
    {limits : Limits} {index : Nat} {slots : List (Option Bytes)}
    (read : checked.readGroup limits index = .ok slots) : ∃ group, GroupWire checked limits index group slots :=
  Proofs.Formats.Parquet.Plain.ByteArray.File.readGroup_wire read

/-- File batches follow the order of the checked group cursor and contain
exactly its successful prefix, with the original failure as the terminal cause. -/
theorem readAll_order {limits : Limits} {source : Bytes} {name : String} {layout : FlatColumn.Layout}
    {checked : Checked name layout} (opened : openFile limits source name layout = .ok checked) :
    let groups := Reader.denoteGroups (checked.source limits).readGroup (List.range checked.snapshot.groupCount)
    readAll limits source name layout = .ok
      ⟨schema name layout, ⟨groups.1.map Relational.AlignedColumns.ofRows, groups.2⟩⟩ := by
  rw [readAll, opened]
  exact Reader.readAll_opened (checked.source limits)

end Silmaril.Formats.Parquet.Plain.ByteArray.File
