module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.Thms
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Readback
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Events

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc

open Arrow.RecursiveSchema.Stream.Writer (Readback)
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch projectTrace)
open Arrow.RecursiveSchema.Batch.Rows (Observation)

public section

theorem convert_open_error {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Events.Selection}
    {cause : TwoList.Error} (original : TwoList.openFile schemaLimits input = .error cause) :
    convert schemaLimits limits ipc input selection = .error (.source (.openError cause)) := by
  simp [convert, original, Except.mapError, bind, Except.bind]

/-- The first failure reported by direct Events precedes all output checks.
It carries its complete original address and produces no bytes. -/
theorem convert_source_failure {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Events.Selection}
    {events : Σ source : Signature, Events.Trace source} {error : Events.Error}
    (accepted : Events.read schemaLimits limits input = .ok events)
    (failed : events.2.termination = .readError error) :
    convert schemaLimits limits ipc input selection = .error (.source error) :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.source_failure accepted failed

theorem selectBatch_rowCount (selection : Events.Selection) (batch : Observation) :
    (selectBatch selection batch).rowCount = batch.rowCount := by cases selection <;> rfl

theorem convertSource_readback {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {ipc : Arrow.RecursiveSchema.Batch.Limits}
    {schema : Compiled schemaLimits snapshot} {selection : Events.Selection} {bytes : KBytes}
    (written : convertSource limits ipc schema selection = .ok bytes) :
    ∃ groups, readGroups limits schema (List.range snapshot.groupCount) = .ok groups ∧
      List.Forall₂ (Rows.GroupWire limits schema) (List.range snapshot.groupCount) groups ∧
      Readback ipc (selectSchema selection (Rows.arrowSchema schema.plan))
        (groups.map (selectBatch selection)) bytes :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.convertSource_readback written

/-- Successful native IPC binds the original checked source to the exact
selected schema and ordered batches on the emitted bytes. -/
theorem convert_readback {schemaLimits : Snapshot.Limits}
    {limits : Chunk.Limits} {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : Events.Selection} {bytes : KBytes}
    (written : convert schemaLimits limits ipc input selection = .ok bytes) :
    ∃ opened groups, TwoList.openFile schemaLimits input = .ok opened ∧
      readGroups limits opened.schema (List.range opened.snapshot.groupCount) = .ok groups ∧
      List.Forall₂ (Rows.GroupWire limits opened.schema) (List.range opened.snapshot.groupCount) groups ∧
      Readback ipc (selectSchema selection (Rows.arrowSchema opened.schema.plan))
        (groups.map (selectBatch selection)) bytes :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.convert_readback written

theorem convert_exact_eos {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : Events.Selection} {bytes : KBytes}
    (written : convert schemaLimits limits ipc input selection = .ok bytes) :
    ∃ offset, Arrow.EnvelopeWire ipc.schema.ipc bytes.toList offset .eos ∧ offset + 8 = bytes.len := by
  obtain ⟨_, _, _, _, _, certificate⟩ := convert_readback written
  obtain ⟨_, offset, _, _, _, _, _, eos, extent⟩ := certificate.result
  exact ⟨offset, eos, extent⟩

/-- The selected direct events and the checked native IPC events agree on
declarations, complete ordered batch observations and EOS. -/
theorem agrees_events {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {bytes : KBytes}
    {selection : Events.Selection} {source : Signature} {events : Events.Trace source}
    {native : Σ sig : Signature, Arrow.RecursiveSchema.Stream.Events.Trace sig}
    (accepted : Events.read schemaLimits limits input = .ok ⟨source, events⟩)
    (written : convert schemaLimits limits ipc input selection = .ok bytes)
    (readback : Arrow.RecursiveSchema.Stream.Events.read ipc bytes = .ok native) :
    let projection := selection.columns source
    let view := projectTrace projection events
    Events.readProjected schemaLimits limits input selection = .ok ⟨projection.schema, view⟩ ∧
      declarations projection.schema = declarations native.1 ∧
      view.batches.map eraseBatch = native.2.batches.map eraseBatch ∧
      view.termination = .eos ∧ native.2.termination = .eos :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.agrees_events accepted written readback

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc
