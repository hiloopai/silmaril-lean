module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events.Thms
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Readback
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Thms

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc

open Parquet.Reader.Recursive (Selection)
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch)

public section

theorem convert_open_error {schemaLimits : Snapshot.Limits} {limits : Reader.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection}
    {cause : TwoListStruct.Error} (failed : TwoListStruct.openFile schemaLimits input = .error cause) :
    convert schemaLimits limits ipc input selection = .error (.openError (.openError cause)) := by
  simp [convert, sourceEvents, TwoListStruct.openRequired, failed,
    Arrow.RecursiveSchema.Stream.Events.ToIpc.emit]

/-- Optional Struct elements are admitted by native Events. Strict IPC
export retains its required-element admission gate under both selections. -/
theorem convert_optional_error {schemaLimits : Snapshot.Limits} {limits : Reader.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection}
    {opened : Source schemaLimits input} (original : TwoListStruct.openFile schemaLimits input = .ok opened)
    (optional : opened.schema.plan.element.nullable = true) :
    convert schemaLimits limits ipc input selection = .error (.openError (.openError .structShape)) := by
  simp [convert, sourceEvents, TwoListStruct.openRequired_of_open original, optional,
    Arrow.RecursiveSchema.Stream.Events.ToIpc.emit]

/-- The original native error and complete projected prefix take
precedence under every IPC budget. -/
theorem convert_source_error {schemaLimits : Snapshot.Limits} {limits : Reader.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection}
    {opened : Source schemaLimits input} {source : Signature} {trace : Events.Trace source} {cause : Events.Error}
    (admitted : TwoListStruct.openRequired schemaLimits input = .ok opened)
    (projected : Events.readProjected schemaLimits limits input selection = .ok ⟨source, trace⟩)
    (failed : trace.termination = .readError cause) :
    convert schemaLimits limits ipc input selection = .error (.readError cause (trace.batches.map eraseBatch)) := by
  rw [convert, Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.sourceEvents_eq admitted,
    projected]
  exact Arrow.RecursiveSchema.Stream.Events.ToIpc.emit_read_error failed

theorem convert_readback {schemaLimits : Snapshot.Limits} {limits : Reader.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection} {wire : KBytes}
    (written : convert schemaLimits limits ipc input selection = .ok wire) :
    Readback schemaLimits limits ipc input selection wire :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.convert_readback written

theorem convert_exact_eos {schemaLimits : Snapshot.Limits} {limits : Reader.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection} {wire : KBytes}
    (written : convert schemaLimits limits ipc input selection = .ok wire) :
    ∃ offset, Arrow.EnvelopeWire ipc.schema.ipc wire.toList offset .eos ∧ offset + 8 = wire.len := by
  obtain ⟨_, _, _, _, _, certificate⟩ := (convert_readback written).original
  obtain ⟨_, offset, _, _, _, _, _, eos, extent⟩ := certificate.result
  exact ⟨offset, eos, extent⟩

/-- The returned native events agree with the selected declaration,
exact ordered complete batches and EOS. -/
theorem agrees_events {schemaLimits : Snapshot.Limits} {limits : Reader.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection} {wire : KBytes}
    {events : Σ source : Signature, Events.Trace source}
    {native : Σ source : Signature, Arrow.RecursiveSchema.Stream.Events.Trace source}
    (projected : Events.readProjected schemaLimits limits input selection = .ok events)
    (written : convert schemaLimits limits ipc input selection = .ok wire)
    (readback : Arrow.RecursiveSchema.Stream.Events.read ipc wire = .ok native) :
    declarations native.1 = declarations events.1 ∧
      native.2.batches.map eraseBatch = events.2.batches.map eraseBatch ∧ native.2.termination = .eos :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.agrees_events projected written readback

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc
