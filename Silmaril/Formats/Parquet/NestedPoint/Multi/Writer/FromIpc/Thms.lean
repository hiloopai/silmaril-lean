module

public import Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc.Defs
import Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc

public section

namespace Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc

open Arrow.StructInt32.Stream (Observed Batch)

/-- Binding preserves the positional descriptor, nullable rows and every
explicit batch boundary. The target uses the full signed child widths. -/
theorem bind_exact {observed : Observed Int64} {input : Writer.Input}
    (accepted : bindInput observed = .ok input) :
    input.field = observed.field ∧ input.groups.map (List.map ToIpc.nativeRow) = observed.batches.map Batch.rows :=
  Proofs.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc.bind_exact accepted

/-- Any original IPC failure has precedence over the descriptor and writer checks. -/
theorem convert_source_error {limits : Limits} {wire : KBytes} {cause : Arrow.StructInt32.Stream.Error}
    (failed : Arrow.StructInt32.Stream.readFor .int64 limits.ipc wire = .error cause) :
    convert limits wire = .error (.source cause) := by
  simp [convert, failed, Except.mapError, Bind.bind, Except.bind]

/-- Success consumes the original source through EOS and certifies exact
NestedPoint groups and typed Events in the emitted file. -/
theorem convert_readback {limits : Limits} {wire : KBytes} {output : Writer.Encoded}
    (written : convert limits wire = .ok output) : Readback limits wire output :=
  Proofs.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc.convert_readback written

/-- A successful forward re-emission recovers the original native
descriptor and all logical batches through exact IPC EOS. -/
theorem roundtrip_ipc {limits : Limits} {target : Arrow.ObservationLimits} {wire returned : KBytes}
    {output : Writer.Encoded} (written : convert limits wire = .ok output)
    (reemitted : (ToIpc.convert ⟨limits.parquet.readback, target⟩ output.bytes).wire = .ok returned) :
    ∃ observed restored,
      Arrow.StructInt32.Stream.readFor .int64 limits.ipc wire = .ok observed ∧
      Arrow.StructInt32.Stream.readFor .int64 target returned = .ok restored ∧
      Arrow.StructInt32.Stream.Writer.AgreesFor observed.field (observed.batches.map Batch.rows) restored :=
  Proofs.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc.roundtrip_ipc written reemitted

end Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc
