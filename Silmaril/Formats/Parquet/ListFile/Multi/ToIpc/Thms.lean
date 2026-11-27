module

public import Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.Multi.ToIpc.Correctness

public section

namespace Silmaril.Formats.Parquet.ListFile.Multi.ToIpc

open Silmaril.Relational

/-- Conversion exposes the unchanged checked Parquet event trace. -/
theorem convert_trace (limits : Limits) (source : Bytes) :
    (convert limits source).trace = Multi.readAll limits.parquet source :=
  Proofs.Formats.Parquet.ListFile.Multi.ToIpc.convert_trace limits source

/-- A refused footer has no schema event or IPC carrier. -/
theorem convert_open_error {limits : Limits} {source : Bytes} {cause : ListFile.OpenError}
    (failed : ListFile.openFile limits.parquet.file source = .error cause) :
    (convert limits source).trace = .error (.openFailure cause) ∧
    (convert limits source).wire = .error (.source (.openFailure cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.ToIpc.convert_open_error failed

/-- The first failing group retains precisely the preceding batches and its original indexed cause. -/
theorem convert_first_error {limits : Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal : Nat}
    {groups : List (Reader.RowGroup (ListFile.schema checked) ListFile.Cell)}
    {cause : Multi.GroupError}
    (opened : ListFile.openFile limits.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : before.mapM (Multi.groupSource limits.parquet checked).readGroup = .ok groups)
    (failed : Multi.readGroup limits.parquet.maxGroupSlots checked ordinal = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map AlignedColumns.ofRows, .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  Proofs.Formats.Parquet.ListFile.Multi.ToIpc.convert_first_error opened split earlier failed

/-- The exact checked footer groups, nullable rows and framed native carrier agree through EOS. -/
theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  Proofs.Formats.Parquet.ListFile.Multi.ToIpc.convert_readback h

end Silmaril.Formats.Parquet.ListFile.Multi.ToIpc
