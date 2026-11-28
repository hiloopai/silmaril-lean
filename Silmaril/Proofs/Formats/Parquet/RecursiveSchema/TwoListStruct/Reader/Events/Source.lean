module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Thms
import Silmaril.Formats.Parquet.Reader.Recursive.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events

open Silmaril.Formats
open Parquet
open Parquet.RecursiveSchema.TwoListStruct
open Parquet.RecursiveSchema.TwoListStruct.Reader (Limits)
open Parquet.RecursiveSchema.TwoListStruct.Reader.Events
open Parquet.Reader.Recursive (Selection)
open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Arrow.RecursiveSchema.Stream.Events (Signature eraseBatch declarations fieldName projectTrace)

public theorem readSource_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {schema : Compiled schemaLimits snapshot}
    {events : Σ source : Signature, Trace source}
    (accepted : readSource limits schema = .ok events) : SourceWire limits schema events.1 events.2 := by
  have logical := Parquet.Reader.Recursive.Groups.events_wire accepted
  have groups := logical.completed.groups
  simp only [sourceOf, List.length_map] at groups
  exact ⟨logical, List.Forall₂.imp (fun _ _ => Parquet.RecursiveSchema.TwoListStruct.Reader.readGroup_wire) groups⟩

public theorem read_wire {schemaLimits : Snapshot.Limits} {limits : Limits} {input : Bytes}
    {events : Σ source : Signature, Trace source}
    (accepted : read schemaLimits limits input = .ok events) : FileWire schemaLimits limits input events.1 events.2 := by
  unfold Parquet.RecursiveSchema.TwoListStruct.Reader.Events.read at accepted
  split at accepted
  · contradiction
  · rename_i opened original
    exact ⟨opened, original, readSource_wire accepted⟩

public theorem read_failure {schemaLimits : Snapshot.Limits} {limits : Limits} {input : Bytes}
    {events : Σ source : Signature, Trace source} {ordinal : Nat}
    {cause : Parquet.RecursiveSchema.TwoListStruct.Reader.Error}
    (accepted : read schemaLimits limits input = .ok events)
    (failed : events.2.termination = .readError (.group ordinal cause)) :
    ordinal = events.2.batches.length ∧
      ∃ opened, Parquet.RecursiveSchema.TwoListStruct.openFile schemaLimits input = .ok opened ∧
        Parquet.RecursiveSchema.TwoListStruct.Reader.readGroup limits opened.schema ordinal = .error cause := by
  obtain ⟨opened, original, wire⟩ := (read_wire accepted).original
  obtain ⟨group, originalCause, found, reached, reported⟩ := wire.logical.completed.failure failed
  change Error.group group originalCause = Error.group ordinal cause at reported
  cases reported
  simp only [sourceOf, List.length_map] at found
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  rw [List.getElem?_range (by simpa using bound)] at found
  exact ⟨(Option.some.inj found).symm, opened, original, reached⟩

public theorem readProjected_wire {schemaLimits : Snapshot.Limits} {limits : Limits} {input : Bytes}
    {events : Σ source : Signature, Trace source} {selection : Selection}
    (accepted : readProjected schemaLimits limits input selection = .ok events) :
    ∃ (source : Signature) (trace : Trace source) (opened : Source schemaLimits input),
      Parquet.RecursiveSchema.TwoListStruct.openFile schemaLimits input = .ok opened ∧
      SourceWire limits opened.schema source trace ∧
      events = ⟨(selection.columns source).schema, projectTrace (selection.columns source) trace⟩ ∧
      declarations events.1 =
        (selection.schema opened.schema.plan.arrow).fields.map (fun field => (fieldName field, field)) ∧
      events.2.batches.map eraseBatch = (trace.batches.map eraseBatch).map selection.batch ∧
      events.2.termination = trace.termination := by
  cases original : read schemaLimits limits input with
  | error cause => simp [readProjected, Arrow.RecursiveSchema.Stream.Events.project, original, Except.map] at accepted
  | ok full =>
    obtain ⟨source, trace⟩ := full
    have equality : ⟨(selection.columns source).schema, projectTrace (selection.columns source) trace⟩ = events := by
      simpa [readProjected, Arrow.RecursiveSchema.Stream.Events.project, original, Except.map] using accepted
    obtain ⟨opened, admitted, wire⟩ := (read_wire original).original
    subst events
    exact ⟨source, trace, opened, admitted, wire, rfl,
      selection.declarations_exact wire.logical.fieldsExact, selection.batches_exact trace, rfl⟩

public theorem readSource_eq_of_complete {leftLimits rightLimits : Limits}
    {leftSchemaLimits rightSchemaLimits : Snapshot.Limits} {leftSnapshot rightSnapshot : Snapshot.Checked}
    {left : Compiled leftSchemaLimits leftSnapshot} {right : Compiled rightSchemaLimits rightSnapshot}
    {groups : List Observation} (fields : left.plan.arrow.fields = right.plan.arrow.fields)
    (before : Parquet.RecursiveSchema.TwoListStruct.Reader.readAll leftLimits left = .ok groups)
    (after : Parquet.RecursiveSchema.TwoListStruct.Reader.readAll rightLimits right = .ok groups) :
    readSource leftLimits left = readSource rightLimits right := by
  have leftCount : leftSnapshot.groupCount = groups.length := by
    simpa using (Parquet.RecursiveSchema.TwoListStruct.Reader.readAll_wire before).length_eq
  have rightCount : rightSnapshot.groupCount = groups.length := by
    simpa using (Parquet.RecursiveSchema.TwoListStruct.Reader.readAll_wire after).length_eq
  exact Parquet.Reader.Recursive.Groups.events_eq_of_complete fields
    (congrArg List.range (leftCount.trans rightCount.symm)) before after

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events
