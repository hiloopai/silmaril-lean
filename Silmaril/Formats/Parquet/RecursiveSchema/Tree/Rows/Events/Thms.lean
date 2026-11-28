module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.Defs
public import Silmaril.Formats.Parquet.Reader.Recursive.Thms
public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms
public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events

open Silmaril.Relational
open Arrow.RecursiveSchema.Stream.Events (Signature BatchEvent eraseBatch projectTrace)

public section

theorem read_open_error {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {input : Bytes}
    {cause : Repeated.Error} (original : Tree.openFile schemaLimits input = .error cause) :
    read schemaLimits limits input = .error (.openError cause) := by
  simp [read, original]

theorem readProjected_open_error {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {input : Bytes}
    {cause : Repeated.Error} (original : Tree.openFile schemaLimits input = .error cause)
    (selection : (source : Signature) → Scan.Projection source) :
    readProjected schemaLimits limits input selection = .error (.openError cause) := by
  simp [readProjected, Arrow.RecursiveSchema.Stream.Events.project, read_open_error original, Except.map]

/-- Each complete unprojected batch has the original checked native result at its footer group ordinal. -/
theorem readSource_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Rows.Limits} {schema : Compiled schemaLimits snapshot}
    {events : Σ source : Signature, Trace source}
    (accepted : readSource limits schema = .ok events) : SourceWire limits schema events.1 events.2 :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.readSource_wire accepted

/-- The reader retains the checked original opening and ordered group prefix. -/
theorem read_wire {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {input : Bytes}
    {events : Σ source : Signature, Trace source}
    (accepted : read schemaLimits limits input = .ok events) : FileWire schemaLimits limits input events.1 events.2 :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.read_wire accepted

/-- A terminal group error is the exact native refusal after the completed prefix. -/
theorem SourceWire.failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Rows.Limits} {schema : Compiled schemaLimits snapshot}
    {source : Signature} {events : Trace source} {ordinal : Nat} {cause : Rows.Error}
    (wire : SourceWire limits schema source events)
    (failed : events.termination = .readError (.group ordinal cause)) :
    ordinal = events.batches.length ∧ Rows.readGroupChecked schema limits ordinal = .error cause :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.SourceWire.failure wire failed

/-- Column selection and selection of erased logical row positions give the same batch. -/
theorem erase_projectColumns {source : Signature} (selection : Scan.Projection source)
    (batch : BatchEvent source) : eraseBatch (selection.projectColumns batch) =
      projectObservation selection (eraseBatch batch) :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.erase_projectColumns selection batch

/-- Selection preserves batch boundaries and produces the exact ordered logical views. -/
theorem projected_observations {source : Signature} (selection : Scan.Projection source)
    (events : Trace source) :
    (projectTrace selection events).batches.map eraseBatch =
      (events.batches.map eraseBatch).map (projectObservation selection) :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.projected_observations selection events

/-- A projected stream has the same checked native prefix, declarations by position, and terminal outcome. -/
theorem readProjected_wire {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {events : Σ source : Signature, Trace source}
    (accepted : readProjected schemaLimits limits input selection = .ok events) :
    ProjectedWire schemaLimits limits input selection events :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.readProjected_wire accepted

/-- Each projected batch is the ordered view of the exact checked native result at that position. -/
theorem ProjectedWire.groups {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {events : Σ source : Signature, Trace source}
    (wire : ProjectedWire schemaLimits limits input selection events) :
    ∃ source opened, Tree.openFile schemaLimits input = .ok opened ∧
      List.Forall₂ (fun group batch => ∃ result,
        Rows.readGroupChecked opened.schema limits group = .ok result ∧
        batch = projectObservation (selection source) result.observation)
        ((List.range opened.snapshot.groupCount).take events.2.batches.length)
        (events.2.batches.map eraseBatch) :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.ProjectedWire.groups wire

/-- Projection retains the original reached group and native cause, including at width zero. -/
theorem projected_failure {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {events : Σ source : Signature, Trace source}
    {ordinal : Nat} {cause : Rows.Error} (wire : ProjectedWire schemaLimits limits input selection events)
    (failed : events.2.termination = .readError (.group ordinal cause)) :
    ordinal = events.2.batches.length ∧
      ∃ opened, Tree.openFile schemaLimits input = .ok opened ∧
        Rows.readGroupChecked opened.schema limits ordinal = .error cause :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.projected_failure wire failed

theorem readSource_complete {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Rows.Limits} {schema : Compiled schemaLimits snapshot}
    {events : Σ source : Signature, Trace source}
    (accepted : readSource limits schema = .ok events) :
    events.2.termination = .eos ↔
      (List.range snapshot.groupCount).mapM (Rows.readGroup schema limits) = .ok (events.2.batches.map eraseBatch) :=
  (readSource_wire accepted).logical.completed.complete

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events
