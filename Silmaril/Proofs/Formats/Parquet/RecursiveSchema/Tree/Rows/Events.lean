module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Events.Defs
public import Silmaril.Formats.Parquet.Reader.Recursive.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Thms
import Silmaril.Semantics.Relational.Scan.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events

open Silmaril.Formats
open Parquet Parquet.RecursiveSchema.Tree
open Parquet.RecursiveSchema.Tree.Rows.Events
open Silmaril.Relational
open Arrow.RecursiveSchema.Stream.Events (Signature BatchEvent eraseBatch eraseRow declarations projectTrace)

public theorem readSource_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Rows.Limits} {schema : Compiled schemaLimits snapshot}
    {events : Σ source : Signature, Trace source}
    (accepted : readSource limits schema = .ok events) : SourceWire limits schema events.1 events.2 := by
  have logical := Parquet.Reader.Recursive.Groups.events_wire accepted
  have groups := logical.completed.groups
  simp only [sourceOf, List.length_map] at groups
  exact ⟨logical, List.Forall₂.imp (fun _ _ => Rows.readGroup_checked) groups⟩

public theorem read_wire {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {input : Bytes}
    {events : Σ source : Signature, Trace source}
    (accepted : read schemaLimits limits input = .ok events) : FileWire schemaLimits limits input events.1 events.2 := by
  unfold Rows.Events.read at accepted
  split at accepted
  · contradiction
  · rename_i opened original
    exact ⟨opened, original, readSource_wire accepted⟩

public theorem SourceWire.failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Rows.Limits} {schema : Compiled schemaLimits snapshot}
    {source : Signature} {events : Trace source} {ordinal : Nat} {cause : Rows.Error}
    (wire : SourceWire limits schema source events)
    (failed : events.termination = .readError (.group ordinal cause)) :
    ordinal = events.batches.length ∧ Rows.readGroupChecked schema limits ordinal = .error cause := by
  obtain ⟨group, originalCause, found, reached, reported⟩ := wire.logical.completed.failure failed
  change Error.group group originalCause = Error.group ordinal cause at reported
  cases reported
  simp only [sourceOf, List.length_map] at found
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  rw [List.getElem?_range (by simpa using bound)] at found
  refine ⟨(Option.some.inj found).symm, ?_⟩
  change Rows.readGroup schema limits ordinal = .error cause at reached
  unfold Rows.readGroup at reached
  cases decoded : Rows.readGroupChecked schema limits ordinal with
  | ok result => simp [decoded, Except.map] at reached
  | error refusal =>
    simp [decoded, Except.map] at reached
    exact congrArg Except.error reached

private theorem erase_projectRow {source : Signature} (selection : Scan.Projection source)
    (row : Scan.Row source Arrow.RecursiveSchema.Stream.Events.Value) :
    eraseRow (selection.projectRow row) =
      List.ofFn (fun i => (eraseRow row)[(selection.index i).val]?.getD none) := by
  unfold eraseRow
  apply congrArg List.ofFn
  funext i
  rw [List.getElem?_ofFn, dite_eq_left (selection.index i).isLt]
  rfl

public theorem erase_projectColumns {source : Signature} (selection : Scan.Projection source)
    (batch : BatchEvent source) : eraseBatch (selection.projectColumns batch) =
      projectObservation selection (eraseBatch batch) := by
  have rows : (selection.projectColumns batch).toRows = selection.project batch.toRows :=
    selection.rowsEquiv_projectColumns batch
  simp only [eraseBatch, projectObservation, Scan.Projection.rowCount_projectColumns,
    rows, Scan.Projection.project, List.map_map, Function.comp_def, erase_projectRow]

public theorem projected_observations {source : Signature} {Failure : Type} (selection : Scan.Projection source)
    (events : Arrow.Events.Trace source Arrow.RecursiveSchema.Stream.Events.Value Failure) :
    (projectTrace selection events).batches.map eraseBatch =
      (events.batches.map eraseBatch).map (projectObservation selection) := by
  simp only [projectTrace, List.map_map, Function.comp_def, erase_projectColumns]

public theorem readProjected_wire {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {events : Σ source : Signature, Trace source}
    (accepted : readProjected schemaLimits limits input selection = .ok events) :
    ProjectedWire schemaLimits limits input selection events := by
  cases original : read schemaLimits limits input with
  | error cause =>
    simp [readProjected, Arrow.RecursiveSchema.Stream.Events.project, original, Except.map] at accepted
  | ok full =>
    obtain ⟨source, trace⟩ := full
    have equality : ⟨(selection source).schema, projectTrace (selection source) trace⟩ = events := by
      simpa [readProjected, Arrow.RecursiveSchema.Stream.Events.project, original, Except.map] using accepted
    obtain ⟨opened, admitted, wire⟩ := (read_wire original).original
    subst events
    exact ⟨source, trace, opened, admitted, wire, rfl, rfl, projected_observations _ _, rfl⟩

public theorem ProjectedWire.groups {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {events : Σ source : Signature, Trace source}
    (wire : ProjectedWire schemaLimits limits input selection events) :
    ∃ source opened, Parquet.RecursiveSchema.Tree.openFile schemaLimits input = .ok opened ∧
      List.Forall₂ (fun group batch => ∃ result,
        Rows.readGroupChecked opened.schema limits group = .ok result ∧
        batch = projectObservation (selection source) result.observation)
        ((List.range opened.snapshot.groupCount).take events.2.batches.length)
        (events.2.batches.map eraseBatch) := by
  obtain ⟨source, trace, opened, admitted, original, selected, _, batches, _⟩ := wire.original
  refine ⟨source, opened, admitted, ?_⟩
  rw [batches, List.forall₂_map_right_iff]
  have count : events.2.batches.length = trace.batches.length := by
    rw [selected]
    simp [projectTrace]
  rw [count]
  exact original.groups.imp fun _ _ ⟨result, accepted, equal⟩ =>
    ⟨result, accepted, congrArg (projectObservation (selection source)) equal.symm⟩

public theorem projected_failure {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {input : Bytes}
    {selection : (source : Signature) → Scan.Projection source} {events : Σ source : Signature, Trace source}
    {ordinal : Nat} {cause : Rows.Error} (wire : ProjectedWire schemaLimits limits input selection events)
    (failed : events.2.termination = .readError (.group ordinal cause)) :
    ordinal = events.2.batches.length ∧
      ∃ opened, Parquet.RecursiveSchema.Tree.openFile schemaLimits input = .ok opened ∧
        Rows.readGroupChecked opened.schema limits ordinal = .error cause := by
  obtain ⟨source, trace, opened, original, checked, equality, _, _, termination⟩ := wire.original
  obtain ⟨reached, failure⟩ := SourceWire.failure checked (termination.symm.trans failed)
  subst events
  exact ⟨by simpa [projectTrace] using reached, opened, original, failure⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Rows.Events
