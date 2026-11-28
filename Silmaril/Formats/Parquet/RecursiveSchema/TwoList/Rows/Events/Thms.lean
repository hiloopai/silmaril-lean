module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms
import Silmaril.Formats.Arrow.Events.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.Prefix
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.Reframe

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events

open Arrow.RecursiveSchema.Stream.Events (Signature eraseBatch projectTrace)

public section

theorem read_open_error {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits} {bytes : Bytes}
    {cause : TwoList.Error} (original : TwoList.openFile schemaLimits bytes = .error cause) :
    read schemaLimits limits bytes = .error (.openError cause) := by
  simp [read, original]

theorem readProjected_open_error {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits} {bytes : Bytes}
    {cause : TwoList.Error} (original : TwoList.openFile schemaLimits bytes = .error cause)
    (selection : Selection) :
    readProjected schemaLimits limits bytes selection = .error (.openError cause) := by
  simp [readProjected, Arrow.RecursiveSchema.Stream.Events.project, read_open_error original, Except.map]

theorem readSource_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot}
    {events : Σ source : Signature, Trace source}
    (accepted : readSource limits schema = .ok events) :
    SourceWire limits schema events.1 events.2 :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.readSource_wire accepted

/-- Every emitted batch is the whole original group. The opened trace
terminates at the first source failure or at EOS after the final group. -/
theorem read_wire {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits} {bytes : Bytes}
    {events : Σ source : Signature, Trace source}
    (accepted : read schemaLimits limits bytes = .ok events) :
    FileWire schemaLimits limits bytes events.1 events.2 :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.read_wire accepted

theorem read_failure {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits} {bytes : Bytes}
    {events : Σ source : Signature, Trace source} {ordinal : Nat} {cause : Rows.Error}
    (accepted : read schemaLimits limits bytes = .ok events)
    (failed : events.2.termination = .readError (.group ordinal cause)) :
    ordinal = events.2.batches.length ∧
      ∃ opened, TwoList.openFile schemaLimits bytes = .ok opened ∧
        Rows.readGroup limits opened.schema ordinal = .error cause :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.read_failure accepted failed

theorem readSource_complete {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot}
    {events : Σ source : Signature, Trace source}
    (accepted : readSource limits schema = .ok events) :
    events.2.termination = .eos ↔ Rows.readAll limits schema = .ok (events.2.batches.map eraseBatch) :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.source_complete accepted

/-- Both projections preserve the original per-group counts and terminal,
and project every row of the same complete prefix. -/
theorem readProjected_preserves {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {bytes : Bytes} {source : Signature} {events : Trace source}
    (accepted : read schemaLimits limits bytes = .ok ⟨source, events⟩) (selection : Selection) :
    let projection := selection.columns source
    let view := projectTrace projection events
    readProjected schemaLimits limits bytes selection = .ok ⟨projection.schema, view⟩ ∧
      view.batches.map (·.rowCount) = events.batches.map (·.rowCount) ∧
      view.termination = events.termination ∧ view.rows = projection.project events.rows :=
  ⟨by simp [readProjected, Arrow.RecursiveSchema.Stream.Events.project, accepted, Except.map],
    Arrow.RecursiveSchema.Stream.Events.projectTrace_counts _ _, rfl,
    Arrow.RecursiveSchema.Stream.Events.projectTrace_rows _ _⟩

/-- Legal V1 reframings of every original group agree in the shared schema,
ordered rows and termination observation. The event traces also agree. -/
theorem readSource_reframe {leftSchemaLimits rightSchemaLimits : Snapshot.Limits}
    {leftSnapshot rightSnapshot : Snapshot.Checked}
    {leftLimits rightLimits : Chunk.Limits}
    {left : Compiled leftSchemaLimits leftSnapshot} {right : Compiled rightSchemaLimits rightSnapshot}
    (comparison : Reframe leftLimits left rightLimits right) :
    Arrow.Events.EventStream.Equivalent (readSource leftLimits left) (readSource rightLimits right) :=
  congrArg Arrow.Events.EventStream.collect
    (Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.reframe comparison)

theorem readProjected_reframe {leftSchemaLimits rightSchemaLimits : Snapshot.Limits}
    {leftLimits rightLimits : Chunk.Limits} {leftBytes rightBytes : Bytes}
    {left : Source leftSchemaLimits leftBytes} {right : Source rightSchemaLimits rightBytes}
    (leftOpen : TwoList.openFile leftSchemaLimits leftBytes = .ok left)
    (rightOpen : TwoList.openFile rightSchemaLimits rightBytes = .ok right)
    (comparison : Reframe leftLimits left.schema rightLimits right.schema) (selection : Selection) :
    Arrow.Events.EventStream.Equivalent (readProjected leftSchemaLimits leftLimits leftBytes selection)
      (readProjected rightSchemaLimits rightLimits rightBytes selection) := by
  unfold Arrow.Events.EventStream.Equivalent readProjected read
  rw [leftOpen, rightOpen]
  dsimp only
  rw [Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.reframe comparison]

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events
