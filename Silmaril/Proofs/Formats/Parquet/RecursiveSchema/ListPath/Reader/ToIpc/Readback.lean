module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc

open Silmaril.Formats
open Parquet
open Parquet.RecursiveSchema.ListPath
open Parquet.RecursiveSchema.ListPath.Reader.ToIpc
open Parquet.RecursiveSchema.ListPath.Reader
open Parquet.Reader.Recursive (Selection)
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch fieldName projectTrace)

private theorem source_ok {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : Selection} {wire : KBytes}
    (written : convert schemaLimits limits ipc input selection = .ok wire) :
    ∃ (source : Signature) (trace : Events.Trace source),
      Events.read schemaLimits limits input = .ok ⟨source, trace⟩ := by
  cases read : Events.read schemaLimits limits input with
  | error cause =>
    simp [convert, Events.readProjected, Arrow.RecursiveSchema.Stream.Events.project, read,
      Except.map, Arrow.RecursiveSchema.Stream.Events.ToIpc.emit] at written
  | ok original =>
    obtain ⟨source, trace⟩ := original
    exact ⟨source, trace, rfl⟩

private theorem writer_readback {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection} {wire : KBytes}
    {source : Signature} {trace : Events.Trace source}
    (direct : Events.read schemaLimits limits input = .ok ⟨source, trace⟩)
    (written : convert schemaLimits limits ipc input selection = .ok wire) :
    let view := projectTrace (selection.columns source) trace
    trace.termination = .eos ∧ Arrow.RecursiveSchema.Stream.Writer.Readback ipc
      (Arrow.RecursiveSchema.Stream.Events.ToIpc.schemaOf (selection.columns source).schema)
      (view.batches.map eraseBatch) wire := by
  have projected := (Events.readProjected_preserves direct selection).1
  exact Arrow.RecursiveSchema.Stream.Events.ToIpc.emit_readback
    (by simpa [convert, projected] using written)

public theorem convert_readback {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes}
    {selection : Selection} {wire : KBytes}
    (written : convert schemaLimits limits ipc input selection = .ok wire) :
    Readback schemaLimits limits ipc input selection wire := by
  obtain ⟨source, trace, direct⟩ := source_ok written
  obtain ⟨opened, original, sourceWire⟩ := (Events.read_wire direct).original
  obtain ⟨ended, certificate⟩ := writer_readback direct written
  have groups : Parquet.RecursiveSchema.ListPath.Reader.readAll limits opened.schema =
      .ok (trace.batches.map eraseBatch) := sourceWire.logical.completed.complete.mp ended
  have schema := Arrow.RecursiveSchema.Stream.Events.ToIpc.schemaOf_exact (selection.declarations_exact sourceWire.logical.fieldsExact)
  rw [schema, selection.batches_exact trace] at certificate
  exact ⟨opened, trace.batches.map eraseBatch, original, groups,
    Parquet.RecursiveSchema.ListPath.Reader.readAll_wire groups, certificate⟩

public theorem agrees_events {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection} {wire : KBytes}
    {events : Σ source : Signature, Events.Trace source}
    {native : Σ source : Signature, Arrow.RecursiveSchema.Stream.Events.Trace source}
    (projected : Events.readProjected schemaLimits limits input selection = .ok events)
    (written : convert schemaLimits limits ipc input selection = .ok wire)
    (readback : Arrow.RecursiveSchema.Stream.Events.read ipc wire = .ok native) :
    declarations native.1 = declarations events.1 ∧
      native.2.batches.map eraseBatch = events.2.batches.map eraseBatch ∧ native.2.termination = .eos := by
  obtain ⟨source, trace, direct⟩ := source_ok written
  obtain ⟨_, _, sourceWire⟩ := (Events.read_wire direct).original
  have view := (Events.readProjected_preserves direct selection).1
  cases Except.ok.inj (projected.symm.trans view)
  have declared := selection.declarations_exact sourceWire.logical.fieldsExact
  have schema := Arrow.RecursiveSchema.Stream.Events.ToIpc.schemaOf_exact declared
  have names : declarations (selection.columns source).schema =
      (Arrow.RecursiveSchema.Stream.Events.ToIpc.schemaOf (selection.columns source).schema).fields.map
        (fun field => (fieldName field, field)) := by
    rw [schema]
    exact declared
  exact Arrow.RecursiveSchema.Stream.Events.ToIpc.agrees_events names
    (by simpa [convert, view] using written) readback

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.ToIpc
