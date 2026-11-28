module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc.Readback
import Silmaril.Semantics.Relational.Table.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events
  (Signature Value declarations fieldName eraseBatch eraseRow projectTrace projectTrace_id)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation)
open Silmaril.Relational

private theorem readGroups_cons {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot} {ordinal : Nat} {rest : List Nat} :
    readGroups limits schema (ordinal :: rest) =
      match Rows.readGroup limits schema ordinal with
      | .error cause => .error (.group ordinal cause)
      | .ok batch => (readGroups limits schema rest).map (batch :: ·) := by
  unfold readGroups
  rw [List.mapM_cons]
  cases Rows.readGroup limits schema ordinal
  · rfl
  · cases rest.mapM (fun index => (Rows.readGroup limits schema index).mapError (Rows.Events.Error.group index))
    all_goals rfl

private theorem prefix_failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot} {ordinals : List Nat}
    {batches : List Observation} {terminal : Arrow.Events.Termination Rows.Events.Error}
    {error : Rows.Events.Error}
    (groupWire : Rows.Events.GroupPrefix limits schema ordinals batches terminal)
    (failed : terminal = .readError error) :
    readGroups limits schema ordinals = .error error := by
  induction groupWire with
  | eos => contradiction
  | failed original =>
    cases failed
    rw [readGroups_cons, original]
  | more original _ _ ih =>
    rw [readGroups_cons, original, ih failed]
    rfl

private theorem prefix_success {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot} {ordinals : List Nat}
    {batches groups : List Observation} {terminal : Arrow.Events.Termination Rows.Events.Error}
    (groupWire : Rows.Events.GroupPrefix limits schema ordinals batches terminal)
    (accepted : readGroups limits schema ordinals = .ok groups) :
    batches = groups ∧ terminal = .eos := by
  induction groupWire generalizing groups with
  | eos => exact ⟨Except.ok.inj accepted, rfl⟩
  | failed original =>
    rw [readGroups_cons, original] at accepted
    contradiction
  | @more ordinal rest batch batches terminal first _ _ ih =>
    rw [readGroups_cons, first] at accepted
    cases tail : readGroups limits schema rest with
    | error error =>
      rw [tail] at accepted
      contradiction
    | ok remaining =>
      have result := ih tail
      rw [tail] at accepted
      exact ⟨(congrArg (batch :: ·) result.1).trans (Except.ok.inj accepted), result.2⟩

public theorem source_failure {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Rows.Events.Selection}
    {events : Σ source : Signature, Rows.Events.Trace source} {error : Rows.Events.Error}
    (accepted : Rows.Events.read schemaLimits limits input = .ok events)
    (failed : events.2.termination = .readError error) :
    convert schemaLimits limits ipc input selection = .error (.source error) := by
  obtain ⟨opened, original, wire⟩ := (Rows.Events.read_wire accepted).original
  have failure := prefix_failure wire.groups failed
  simp [convert, original, convertSource, failure, Except.mapError, bind, Except.bind]

private theorem selected_fields (selection : Rows.Events.Selection) {source : Signature}
    {schema : Arrow.RecursiveSchema.Schema}
    (original : declarations source = schema.fields.map (fun field => (fieldName field, field))) :
    declarations (selection.columns source).schema =
      (selectSchema selection schema).fields.map (fun field => (fieldName field, field)) := by
  cases selection
  · exact original
  · rfl

private theorem map_const {α β : Type} (rows : List α) (value : β) :
    rows.map (fun _ => value) = List.replicate rows.length value := by
  induction rows <;> simp_all [List.replicate_succ]

private theorem empty_batch {source : Signature} (batch : Arrow.Events.Batch source Value) :
    eraseBatch ((Rows.Events.Selection.empty.columns source).projectColumns batch) =
      selectBatch .empty (eraseBatch batch) := by
  let columns := (Rows.Events.Selection.empty.columns source).projectColumns batch
  have erased : ∀ row : Scan.Row (Rows.Events.Selection.empty.columns source).schema Value,
      eraseRow row = [] := fun _ => rfl
  change ⟨columns.rowCount, columns.toRows.map eraseRow⟩ = selectBatch .empty (eraseBatch batch)
  have allRows : columns.toRows.map eraseRow = columns.toRows.map (fun _ => []) :=
    List.map_congr_left (fun row _ => erased row)
  rw [allRows, map_const, AlignedColumns.length_toRows]
  rfl

private theorem selected_batches {source : Signature} (selection : Rows.Events.Selection)
    (events : Rows.Events.Trace source) :
    (projectTrace (selection.columns source) events).batches.map eraseBatch =
      (events.batches.map eraseBatch).map (selectBatch selection) := by
  cases selection
  · rw [Rows.Events.Selection.columns, projectTrace_id]
    simp only [List.map_map]
    rfl
  · simp only [projectTrace, List.map_map]
    exact List.map_congr_left (fun batch _ => empty_batch batch)

public theorem agrees_events {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {bytes : KBytes}
    {selection : Rows.Events.Selection} {source : Signature} {events : Rows.Events.Trace source}
    {native : Σ sig : Signature, Arrow.RecursiveSchema.Stream.Events.Trace sig}
    (accepted : Rows.Events.read schemaLimits limits input = .ok ⟨source, events⟩)
    (written : convert schemaLimits limits ipc input selection = .ok bytes)
    (readback : Arrow.RecursiveSchema.Stream.Events.read ipc bytes = .ok native) :
    let projection := selection.columns source
    let view := projectTrace projection events
    Rows.Events.readProjected schemaLimits limits input selection = .ok ⟨projection.schema, view⟩ ∧
      declarations projection.schema = declarations native.1 ∧
      view.batches.map eraseBatch = native.2.batches.map eraseBatch ∧
      view.termination = .eos ∧ native.2.termination = .eos := by
  obtain ⟨opened, groups, original, read, _, certificate⟩ := convert_readback written
  obtain ⟨other, otherOpen, wire⟩ := (Rows.Events.read_wire accepted).original
  cases Except.ok.inj (otherOpen.symm.trans original)
  obtain ⟨same, ending⟩ := prefix_success wire.groups read
  obtain ⟨trace, offset, strict, _, fields, batches, eos, _, _⟩ := certificate.result
  obtain ⟨nativeFields, nativeBatches, nativeEnd⟩ :=
    Arrow.RecursiveSchema.Stream.Events.read_checked_eos strict eos readback
  refine ⟨(Rows.Events.readProjected_preserves accepted selection).1, ?_, ?_, ending, nativeEnd⟩
  · exact (selected_fields selection wire.fields).trans (nativeFields.trans (by rw [fields])).symm
  · exact (selected_batches selection events).trans ((congrArg (List.map (selectBatch selection)) same).trans
      (nativeBatches.trans batches).symm)

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.ToIpc
