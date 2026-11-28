module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Thms
import Silmaril.Formats.Parquet.Reader.Recursive.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events

open Silmaril.Formats
open Parquet
open Parquet.RecursiveSchema.ListPath
open Parquet.RecursiveSchema.ListPath.Reader.Events
open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Arrow.RecursiveSchema.Stream.Events (Signature eraseBatch)

public theorem readSource_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot}
    {events : Σ source : Signature, Trace source}
    (accepted : readSource limits schema = .ok events) : SourceWire limits schema events.1 events.2 := by
  have logical := Parquet.Reader.Recursive.Groups.events_wire accepted
  have groups := logical.completed.groups
  simp only [sourceOf, List.length_map] at groups
  exact ⟨logical, List.Forall₂.imp (fun _ _ => Parquet.RecursiveSchema.ListPath.Reader.readGroup_wire) groups⟩

public theorem read_wire {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits} {input : Bytes}
    {events : Σ source : Signature, Trace source}
    (accepted : read schemaLimits limits input = .ok events) : FileWire schemaLimits limits input events.1 events.2 := by
  unfold Parquet.RecursiveSchema.ListPath.Reader.Events.read at accepted
  split at accepted
  · contradiction
  · rename_i opened original
    exact ⟨opened, original, readSource_wire accepted⟩

public theorem read_failure {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits} {input : Bytes}
    {events : Σ source : Signature, Trace source} {ordinal : Nat}
    {cause : Parquet.RecursiveSchema.ListPath.Reader.Error}
    (accepted : read schemaLimits limits input = .ok events)
    (failed : events.2.termination = .readError (.group ordinal cause)) :
    ordinal = events.2.batches.length ∧
      ∃ opened, Parquet.RecursiveSchema.ListPath.openFile schemaLimits input = .ok opened ∧
        Parquet.RecursiveSchema.ListPath.Reader.readGroup limits opened.schema ordinal = .error cause := by
  obtain ⟨opened, original, wire⟩ := (read_wire accepted).original
  obtain ⟨group, originalCause, found, reached, reported⟩ := wire.logical.completed.failure failed
  change Error.group group originalCause = Error.group ordinal cause at reported
  cases reported
  simp only [sourceOf, List.length_map] at found
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  rw [List.getElem?_range (by simpa using bound)] at found
  exact ⟨(Option.some.inj found).symm, opened, original, reached⟩

public theorem readSource_eq_of_complete {leftLimits rightLimits : Chunk.Limits}
    {leftSchemaLimits rightSchemaLimits : Snapshot.Limits} {leftSnapshot rightSnapshot : Snapshot.Checked}
    {left : Compiled leftSchemaLimits leftSnapshot} {right : Compiled rightSchemaLimits rightSnapshot}
    {groups : List Observation} (fields : left.plan.arrow.fields = right.plan.arrow.fields)
    (before : Parquet.RecursiveSchema.ListPath.Reader.readAll leftLimits left = .ok groups)
    (after : Parquet.RecursiveSchema.ListPath.Reader.readAll rightLimits right = .ok groups) :
    readSource leftLimits left = readSource rightLimits right := by
  have leftCount : leftSnapshot.groupCount = groups.length := by
    simpa using (Parquet.RecursiveSchema.ListPath.Reader.readAll_wire before).length_eq
  have rightCount : rightSnapshot.groupCount = groups.length := by
    simpa using (Parquet.RecursiveSchema.ListPath.Reader.readAll_wire after).length_eq
  exact Parquet.Reader.Recursive.Groups.events_eq_of_complete fields
    (congrArg List.range (leftCount.trans rightCount.symm)) before after

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events
