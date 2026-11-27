module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Readback

@[expose] public section

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc

theorem convert_source_error {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Rows.Limits} {ipc : Arrow.RecursiveSchema.Batch.Limits}
    {schema : Compiled schemaLimits snapshot} {cause : Rows.Error}
    (failed : Rows.readAll limits schema = .error cause) :
    convert limits ipc schema = .error (.source cause) := by
  simp [convert, failed, Except.mapError, bind, Except.bind]

theorem convert_readback {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Rows.Limits} {ipc : Arrow.RecursiveSchema.Batch.Limits}
    {schema : Compiled schemaLimits snapshot} {bytes : KBytes}
    (written : convert limits ipc schema = .ok bytes) :
    ∃ groups, Rows.readAll limits schema = .ok groups ∧
      List.Forall₂ (Rows.GroupWire limits schema) (List.range snapshot.groupCount) groups ∧
      Arrow.RecursiveSchema.Stream.Writer.Readback ipc schema.arrow groups bytes :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.convert_readback written

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc
