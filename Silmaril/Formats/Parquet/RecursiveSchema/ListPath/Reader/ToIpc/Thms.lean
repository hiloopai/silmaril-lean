module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.Thms
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Readback

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc

open Parquet.Reader.Recursive (Selection)
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch projectTrace)

public section

theorem convert_open_error {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection}
    {cause : ListPath.Error} (failed : ListPath.openFile schemaLimits input = .error cause) :
    convert schemaLimits limits ipc input selection = .error (.openError (.openError cause)) := by
  rw [convert, Events.readProjected_open_error failed selection]
  rfl

/-- The original native error and complete projected prefix take
precedence under every IPC budget. -/
theorem convert_source_error {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection}
    {source : Signature} {trace : Events.Trace source} {cause : Events.Error}
    (direct : Events.read schemaLimits limits input = .ok ⟨source, trace⟩)
    (failed : trace.termination = .readError cause) :
    convert schemaLimits limits ipc input selection =
      .error (.readError cause ((trace.batches.map eraseBatch).map selection.batch)) := by
  have projected : (projectTrace (selection.columns source) trace).termination = .readError cause := failed
  rw [convert, (Events.readProjected_preserves direct selection).1,
    Arrow.RecursiveSchema.Stream.Events.ToIpc.emit_read_error projected, selection.batches_exact trace]

theorem convert_readback {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection} {wire : KBytes}
    (written : convert schemaLimits limits ipc input selection = .ok wire) :
    Readback schemaLimits limits ipc input selection wire :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.convert_readback written

theorem convert_exact_eos {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection} {wire : KBytes}
    (written : convert schemaLimits limits ipc input selection = .ok wire) :
    ∃ offset, Arrow.EnvelopeWire ipc.schema.ipc wire.toList offset .eos ∧ offset + 8 = wire.len := by
  obtain ⟨_, _, _, _, _, certificate⟩ := (convert_readback written).original
  obtain ⟨_, offset, _, _, _, _, _, eos, extent⟩ := certificate.result
  exact ⟨offset, eos, extent⟩

/-- The returned native events agree with the selected declaration,
exact ordered complete batches and EOS. -/
theorem agrees_events {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection} {wire : KBytes}
    {events : Σ source : Signature, Events.Trace source}
    {native : Σ source : Signature, Arrow.RecursiveSchema.Stream.Events.Trace source}
    (projected : Events.readProjected schemaLimits limits input selection = .ok events)
    (written : convert schemaLimits limits ipc input selection = .ok wire)
    (readback : Arrow.RecursiveSchema.Stream.Events.read ipc wire = .ok native) :
    declarations native.1 = declarations events.1 ∧
      native.2.batches.map eraseBatch = events.2.batches.map eraseBatch ∧ native.2.termination = .eos :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.agrees_events projected written readback

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc
