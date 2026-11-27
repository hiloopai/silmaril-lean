module

public import Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi.ToIpc.Wire
import Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi.ToIpc.Events

public section

namespace Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc

open Silmaril.Relational
open Arrow.StructInt32 (Field)

/-- The selected names and repetition flags come from the original checked footer items. -/
theorem openFile_wire {limits : SourceLimits} {bytes : Bytes} {checked : Checked}
    (opened : openFile limits bytes = .ok checked) : OpenWire limits bytes checked :=
  Proofs.Formats.Parquet.NestedPoint.Multi.ToIpc.openFile_wire opened

/-- The original sibling definition-level witnesses determine parent absence,
an independent optional wide child, and both signed values in row order. -/
theorem readGroup_wire {limits : Multi.Limits} {snapshot : Snapshot.Checked}
    {ordinal : Nat} {rows : List NestedPoint.Row}
    (decoded : Multi.read limits snapshot ordinal = .ok rows) : GroupWire limits snapshot ordinal rows :=
  Proofs.Formats.Parquet.NestedPoint.Multi.ToIpc.readGroup_wire decoded

/-- The concrete Events observation agrees with the shared ordered group reader. -/
theorem readAll_reader {limits : SourceLimits} {bytes : Bytes} {checked : Checked}
    (opened : openFile limits bytes = .ok checked) :
    readAll limits bytes = Reader.readAll (.ok ⟨schema checked.field, groupSource limits.group checked⟩) :=
  Proofs.Formats.Parquet.NestedPoint.Multi.ToIpc.readAll_reader opened

/-- Emission retains the complete typed Events result, including any source error prefix. -/
theorem convert_trace (limits : Limits) (bytes : Bytes) :
    (convert limits bytes).trace = readAll limits.parquet bytes :=
  Proofs.Formats.Parquet.NestedPoint.Multi.ToIpc.convert_trace limits bytes

/-- An open failure returns the original error without attempting IPC admission. -/
theorem convert_open_error {limits : Limits} {bytes : Bytes} {cause : OpenError}
    (failed : openFile limits.parquet bytes = .error cause) :
    (convert limits bytes).trace = .error (.openFailure cause) ∧
    (convert limits bytes).wire = .error (.source (.openFailure cause)) := by
  simp [convert, failed]

/-- First failure retains the exact completed group prefix and original group,
column and frame cause. It takes priority under every IPC writer budget. -/
theorem convert_first_error {limits : Limits} {bytes : Bytes} {checked : Checked}
    {before after : List Nat} {ordinal : Nat} {groups : List (List NestedPoint.Row)} {cause : Multi.Error}
    (opened : openFile limits.parquet bytes = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : before.mapM (Multi.read limits.parquet.group checked.snapshot) = .ok groups)
    (failed : Multi.read limits.parquet.group checked.snapshot ordinal = .error cause) :
    (convert limits bytes).trace = .ok ⟨schema checked.field,
      ⟨groups.map (AlignedColumns.ofRows ∘ rowsFor checked.field), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits bytes).wire = .error (.source (.groupFailure ordinal cause)) :=
  Proofs.Formats.Parquet.NestedPoint.Multi.ToIpc.convert_first_error opened split earlier failed

/-- Each source group contributes one native batch at its original position. -/
theorem nativeBatches_of_groups (field : Field) (groups : List (List NestedPoint.Row))
    (outcome : Arrow.Events.Termination SourceError) :
    nativeBatches (field := field) ⟨groups.map (AlignedColumns.ofRows ∘ rowsFor field), outcome⟩ =
      groups.map (List.map nativeRow) :=
  Proofs.Formats.Parquet.NestedPoint.Multi.ToIpc.nativeBatches_of_groups field groups outcome

/-- Every successful carrier contains the original source descriptor and
ordered nullable rows, checked through exact native Struct IPC EOS. -/
theorem convert_readback {limits : Limits} {bytes : Bytes} {wire : KBytes}
    (written : (convert limits bytes).wire = .ok wire) : Readback limits bytes wire :=
  Proofs.Formats.Parquet.NestedPoint.Multi.ToIpc.convert_readback written

end Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc
