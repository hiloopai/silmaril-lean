module

public import Silmaril.Formats.Parquet.ListFile.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.Correctness

public section

namespace Silmaril.Formats.Parquet.ListFile

open Silmaril.Formats.ThriftCompact
open Silmaril.Relational

/-- A successful annotation read identifies the original logical field, the sole
LIST union arm and exact empty payload, and any matching converted code. -/
theorem checkList_wire {reader : Traversal.Reader} {outer : Footer.ColumnOrder.Item}
    (h : checkList reader outer = .ok ()) :
    AnnotationWire reader outer :=
  Proofs.Formats.Parquet.ListFile.checkList_wire h

/-- Open binds the original schema ordinals and LIST annotation to one checked footer. -/
theorem openFile_wire {limits : Limits} {source : Bytes} {checked : Checked}
    (h : openFile limits source = .ok checked) : OpenWire limits source checked :=
  Proofs.Formats.Parquet.ListFile.openFile_wire h

/-- The frame list comes from the original checked group and exact chunk. -/
theorem frameGroup_wire {checked : Checked} {index : Nat} {framed : FramedGroup}
    (h : checked.frameGroup index = .ok framed) : FramedGroupWire checked index framed :=
  Proofs.Formats.Parquet.ListFile.frameGroup_wire h

/-- An admitted group uses its original local chunk and complete V1 frame.
The original footer row count and header level-slot count are checked separately. -/
theorem readGroup_wire {checked : Checked} {index : Nat} {slots : List ListPage.Row}
    (h : checked.readGroup index = .ok slots) : GroupWire checked index slots :=
  Proofs.Formats.Parquet.ListFile.readGroup_wire h

/-- The event schema carries the original LIST field name. -/
theorem schema_exact (checked : Checked) :
    (schema checked).width = 1 ∧
      ∀ index : Fin (schema checked).width,
        (schema checked).kind index = (checked.shape.outer.name, .nullableListOfNullableInt32) :=
  Proofs.Formats.Parquet.ListFile.schema_exact checked

/-- The Arrow batch carries all nullable lists and elements in their original order. -/
theorem batch_slots (checked : Checked) (slots : List ListPage.Row)
    (field : Fin (schema checked).width) :
    (AlignedColumns.ofRows (rows checked slots)).rowCount = slots.length ∧
      (AlignedColumns.ofRows (rows checked slots)).values field = slots :=
  Proofs.Formats.Parquet.ListFile.batch_slots checked slots field

/-- Group events carry the original typed cause and the zero-based footer ordinal. -/
theorem rowsAt_error_iff {checked : Checked} {index : Nat} {cause : ReadError} :
    rowsAt checked index = .error (.groupFailure index cause) ↔
      checked.readGroup index = .error cause :=
  Proofs.Formats.Parquet.ListFile.rowsAt_error_iff

/-- An invalid file emits no schema or batch. -/
theorem readAll_open_error {limits : Limits} {source : Bytes} {cause : OpenError}
    (failed : openFile limits source = .error cause) :
    readAll limits source = .error (.openFailure cause) :=
  Proofs.Formats.Parquet.ListFile.readAll_open_error failed

/-- The trace follows the complete group reads in original footer order. -/
theorem readAll_reference {limits : Limits} {source : Bytes} {checked : Checked}
    (opened : openFile limits source = .ok checked) :
    let reference := Reader.denoteGroups (rowsAt checked) (List.range checked.snapshot.groupCount)
    readAll limits source = .ok ⟨schema checked,
      ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩ :=
  Proofs.Formats.Parquet.ListFile.readAll_reference opened

/-- Successful group reads produce one ordered batch per footer group and EOS. -/
theorem readAll_success {limits : Limits} {source : Bytes} {checked : Checked}
    {groups : List (List ListPage.Row)}
    (opened : openFile limits source = .ok checked)
    (decoded : (List.range checked.snapshot.groupCount).mapM checked.readGroup = .ok groups) :
    readAll limits source = .ok ⟨schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows checked), .eos⟩⟩ :=
  Proofs.Formats.Parquet.ListFile.readAll_success opened decoded

/-- A failing group retains precisely the preceding batches and the original typed error. -/
theorem readAll_first_error {limits : Limits} {source : Bytes} {checked : Checked}
    {before after : List Nat} {index : Nat} {groups : List (List ListPage.Row)} {cause : ReadError}
    (opened : openFile limits source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM checked.readGroup = .ok groups)
    (failed : checked.readGroup index = .error cause) :
    readAll limits source = .ok ⟨schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows checked), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.ListFile.readAll_first_error opened split earlier failed

end Silmaril.Formats.Parquet.ListFile
