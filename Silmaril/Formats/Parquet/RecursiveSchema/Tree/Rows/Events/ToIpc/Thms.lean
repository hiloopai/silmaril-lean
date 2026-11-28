module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.Thms
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc

open Silmaril.Relational
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch)
open Arrow.RecursiveSchema.Stream.Events.ToIpc (schemaOf)

public section

theorem convert_open_error {schemaLimits : Snapshot.Limits} {limits : Rows.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source}
    {cause : Repeated.Error} (failed : Tree.openFile schemaLimits input = .error cause) :
    convert schemaLimits limits ipc input selection = .error (.openError (.openError cause)) := by
  rw [convert, Events.readProjected_open_error failed selection]
  rfl

/-- The first source error and its exact selected prefix take precedence under every target budget. -/
theorem convert_source_error {schemaLimits : Snapshot.Limits} {limits : Rows.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source}
    {source : Signature} {trace : Events.Trace source} {cause : Events.Error}
    (projected : Events.readProjected schemaLimits limits input selection = .ok ⟨source, trace⟩)
    (failed : trace.termination = .readError cause) :
    convert schemaLimits limits ipc input selection = .error (.readError cause (trace.batches.map eraseBatch)) := by
  rw [convert, projected]
  exact Arrow.RecursiveSchema.Stream.Events.ToIpc.emit_read_error failed

/-- Strict readback carries the complete native groups, selected observations and declaration. -/
theorem convert_readback {schemaLimits : Snapshot.Limits} {limits : Rows.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {wire : KBytes}
    (written : convert schemaLimits limits ipc input selection = .ok wire) :
    Readback schemaLimits limits ipc input selection wire :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.convert_readback written

/-- Native IPC Events recover the exact selected declaration, ordered batches and EOS. -/
theorem agrees_events {schemaLimits : Snapshot.Limits} {limits : Rows.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {wire : KBytes}
    {selected : Σ source : Signature, Events.Trace source}
    {native : Σ source : Signature, Arrow.RecursiveSchema.Stream.Events.Trace source}
    (projected : Events.readProjected schemaLimits limits input selection = .ok selected)
    (written : convert schemaLimits limits ipc input selection = .ok wire)
    (readback : Arrow.RecursiveSchema.Stream.Events.read ipc wire = .ok native) :
    declarations native.1 = declarations selected.1 ∧
      native.2.batches.map eraseBatch = selected.2.batches.map eraseBatch ∧ native.2.termination = .eos :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.agrees_events projected written readback

/-- The returned prefix and reached native error are certified against the original file. -/
theorem convert_group_failure {schemaLimits : Snapshot.Limits} {limits : Rows.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {ordinal : Nat} {cause : Rows.Error}
    {completedBatches : List Arrow.RecursiveSchema.Batch.Rows.Observation}
    (refused : convert schemaLimits limits ipc input selection = .error (.readError (.group ordinal cause) completedBatches)) :
    ∃ events, Events.readProjected schemaLimits limits input selection = .ok events ∧
      Events.ProjectedWire schemaLimits limits input selection events ∧
      events.2.termination = .readError (.group ordinal cause) ∧ events.2.batches.map eraseBatch = completedBatches ∧
      ordinal = completedBatches.length ∧
      ∃ opened, Tree.openFile schemaLimits input = .ok opened ∧
        Rows.readGroupChecked opened.schema limits ordinal = .error cause :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.convert_group_failure refused

/-- A target refusal is possible only after every native group and exact source EOS. -/
theorem convert_writer_error {schemaLimits : Snapshot.Limits} {limits : Rows.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {cause : Arrow.RecursiveSchema.Stream.Writer.Error}
    (refused : convert schemaLimits limits ipc input selection = .error (.writer cause)) :
    ∃ events, Events.readProjected schemaLimits limits input selection = .ok events ∧
      Completed schemaLimits limits input selection events ∧
      Arrow.RecursiveSchema.Stream.Writer.emit ipc (schemaOf events.1)
        (events.2.batches.map eraseBatch) = .error cause :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc.convert_writer_error refused

theorem convert_exact_eos {schemaLimits : Snapshot.Limits} {limits : Rows.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {wire : KBytes}
    (written : convert schemaLimits limits ipc input selection = .ok wire) :
    ∃ offset, Arrow.EnvelopeWire ipc.schema.ipc wire.toList offset .eos ∧ offset + 8 = wire.len := by
  obtain ⟨_, _, _, certificate⟩ := (convert_readback written).original
  obtain ⟨_, offset, _, _, _, _, _, eos, extent⟩ := certificate.result
  exact ⟨offset, eos, extent⟩

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ToIpc
