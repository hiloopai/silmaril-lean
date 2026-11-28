module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.Defs
public import Silmaril.Formats.Parquet.Reader.Recursive.Thms
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.Source

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events

open Parquet.Reader.Recursive (Selection)
open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Arrow.RecursiveSchema.Stream.Events (Signature eraseBatch projectTrace)

public section

theorem read_open_error {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits} {input : Bytes}
    {cause : ListPath.Error} (original : ListPath.openFile schemaLimits input = .error cause) :
    read schemaLimits limits input = .error (.openError cause) := by
  simp [read, original]

theorem readProjected_open_error {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits} {input : Bytes}
    {cause : ListPath.Error} (original : ListPath.openFile schemaLimits input = .error cause)
    (selection : Selection) :
    readProjected schemaLimits limits input selection = .error (.openError cause) := by
  simp [readProjected, Arrow.RecursiveSchema.Stream.Events.project, read_open_error original, Except.map]

/-- Each emitted batch has its original complete-group wire witness. -/
theorem readSource_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot}
    {events : Σ source : Signature, Trace source}
    (accepted : readSource limits schema = .ok events) : SourceWire limits schema events.1 events.2 :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.readSource_wire accepted

theorem read_wire {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits} {input : Bytes}
    {events : Σ source : Signature, Trace source}
    (accepted : read schemaLimits limits input = .ok events) : FileWire schemaLimits limits input events.1 events.2 :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.read_wire accepted

theorem read_failure {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits} {input : Bytes}
    {events : Σ source : Signature, Trace source} {ordinal : Nat} {cause : Reader.Error}
    (accepted : read schemaLimits limits input = .ok events)
    (failed : events.2.termination = .readError (.group ordinal cause)) :
    ordinal = events.2.batches.length ∧
      ∃ opened, ListPath.openFile schemaLimits input = .ok opened ∧
        Reader.readGroup limits opened.schema ordinal = .error cause :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.read_failure accepted failed

theorem readSource_complete {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot}
    {events : Σ source : Signature, Trace source}
    (accepted : readSource limits schema = .ok events) :
    events.2.termination = .eos ↔ Reader.readAll limits schema = .ok (events.2.batches.map eraseBatch) :=
  (readSource_wire accepted).logical.completed.complete

/-- Both selections project the same complete prefix, preserving each
original group count and the terminal outcome. -/
theorem readProjected_preserves {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {input : Bytes} {source : Signature} {events : Trace source}
    (accepted : read schemaLimits limits input = .ok ⟨source, events⟩) (selection : Selection) :
    let projection := selection.columns source
    let view := projectTrace projection events
    readProjected schemaLimits limits input selection = .ok ⟨projection.schema, view⟩ ∧
      view.batches.map (·.rowCount) = events.batches.map (·.rowCount) ∧
      view.termination = events.termination ∧ view.rows = projection.project events.rows :=
  ⟨by simp [readProjected, Arrow.RecursiveSchema.Stream.Events.project, accepted, Except.map],
    Arrow.RecursiveSchema.Stream.Events.projectTrace_counts _ _, rfl,
    Arrow.RecursiveSchema.Stream.Events.projectTrace_rows _ _⟩

theorem readSource_eq_of_complete {leftLimits rightLimits : Chunk.Limits}
    {leftSchemaLimits rightSchemaLimits : Snapshot.Limits} {leftSnapshot rightSnapshot : Snapshot.Checked}
    {left : Compiled leftSchemaLimits leftSnapshot} {right : Compiled rightSchemaLimits rightSnapshot}
    {groups : List Observation} (fields : left.plan.arrow.fields = right.plan.arrow.fields)
    (before : Reader.readAll leftLimits left = .ok groups)
    (after : Reader.readAll rightLimits right = .ok groups) :
    readSource leftLimits left = readSource rightLimits right :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.readSource_eq_of_complete fields before after

/-- Accepted reframings with the same declaration and ordered group
observations agree under either projection. -/
theorem readProjected_reframe {leftLimits rightLimits : Chunk.Limits}
    {leftSchemaLimits rightSchemaLimits : Snapshot.Limits} {leftInput rightInput : Bytes}
    {left : Source leftSchemaLimits leftInput} {right : Source rightSchemaLimits rightInput}
    {groups : List Observation}
    (leftOpen : ListPath.openFile leftSchemaLimits leftInput = .ok left)
    (rightOpen : ListPath.openFile rightSchemaLimits rightInput = .ok right)
    (fields : left.schema.plan.arrow.fields = right.schema.plan.arrow.fields)
    (before : Reader.readAll leftLimits left.schema = .ok groups)
    (after : Reader.readAll rightLimits right.schema = .ok groups)
    (selection : Selection) :
    Arrow.Events.EventStream.Equivalent (readProjected leftSchemaLimits leftLimits leftInput selection)
      (readProjected rightSchemaLimits rightLimits rightInput selection) := by
  unfold Arrow.Events.EventStream.Equivalent readProjected read
  rw [leftOpen, rightOpen]
  exact congrArg (fun stream => (Arrow.RecursiveSchema.Stream.Events.project stream selection.columns).collect)
    (readSource_eq_of_complete fields before after)

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events
