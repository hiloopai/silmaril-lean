module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Thms
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events
  (Signature declarations_signature rowsOfBatch eraseBatch eraseBatch_ofBatch ofBatch)
open Silmaril.Relational (AlignedColumns)

private theorem group_error {fields : List Arrow.RecursiveSchema.Field} {group : Nat}
    {result : Except Rows.Error Observation} {cause : Rows.Error}
    {typed : ∀ batch, result = .ok batch →
      ∀ row ∈ batch.rows, Arrow.RecursiveSchema.Batch.Rows.RowFits fields row}
    (failed : result = .error cause) :
    groupRows fields group result typed = .error (.group group cause) := by
  cases failed
  rfl

private theorem group_ok {fields : List Arrow.RecursiveSchema.Field} {group : Nat}
    {result : Except Rows.Error Observation} {batch : Observation}
    {typed : ∀ batch, result = .ok batch →
      ∀ row ∈ batch.rows, Arrow.RecursiveSchema.Batch.Rows.RowFits fields row}
    (accepted : result = .ok batch) :
    groupRows fields group result typed = .ok (rowsOfBatch fields batch (typed batch accepted)) := by
  cases accepted
  rfl

private theorem denote_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) (ordinals : List Nat) :
    let observed := Reader.denoteGroups (readGroup limits schema) ordinals
    GroupPrefix limits schema ordinals
      ((observed.1.map AlignedColumns.ofRows).map eraseBatch) observed.2 := by
  induction ordinals with
  | nil => exact .eos
  | cons group rest tail =>
    cases original : Rows.readGroup limits schema group with
    | error cause =>
      have reached : readGroup limits schema group = .error (.group group cause) :=
        group_error original
      simpa [Reader.denoteGroups, reached] using
        (GroupPrefix.failed (rest := rest) original)
    | ok batch =>
      have wire := Rows.readGroup_wire original
      obtain ⟨_, _, _, _, _, checked⟩ := wire.original
      have reached : readGroup limits schema group = .ok
          (rowsOfBatch (Rows.arrowSchema schema.plan).fields batch checked.typed) :=
        group_ok original
      simp only [Reader.denoteGroups, reached, List.map_cons]
      change GroupPrefix limits schema (group :: rest)
        (eraseBatch (ofBatch _ batch checked.typed) :: _) _
      rw [eraseBatch_ofBatch _ _ _ (checked.count.trans checked.rowCount.symm)]
      exact .more original wire tail

public theorem readSource_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot}
    {events : Σ source : Signature, Trace source}
    (accepted : readSource limits schema = .ok events) : SourceWire limits schema events.1 events.2 := by
  unfold readSource at accepted
  rw [Reader.readAll_opened] at accepted
  have same := Except.ok.inj accepted
  subst events
  exact ⟨declarations_signature _, denote_wire limits schema _⟩

public theorem read_wire {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits} {bytes : Bytes}
    {events : Σ source : Signature, Trace source}
    (accepted : Rows.Events.read schemaLimits limits bytes = .ok events) :
    FileWire schemaLimits limits bytes events.1 events.2 := by
  unfold Rows.Events.read at accepted
  split at accepted
  · contradiction
  · rename_i opened original
    exact ⟨opened, original, readSource_wire accepted⟩

private theorem prefix_failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot} {ordinals : List Nat}
    {observations : List Observation} {ordinal : Nat} {cause : Rows.Error}
    {terminal : Arrow.Events.Termination Rows.Events.Error}
    (groups : GroupPrefix limits schema ordinals observations terminal)
    (failed : terminal = .readError (.group ordinal cause)) :
    ordinals[observations.length]? = some ordinal ∧
      Rows.readGroup limits schema ordinal = .error cause := by
  induction groups with
  | eos => contradiction
  | failed original =>
    cases failed
    exact ⟨rfl, original⟩
  | more _ _ _ tail => exact tail failed

public theorem read_failure {schemaLimits : Snapshot.Limits} {limits : Chunk.Limits} {bytes : Bytes}
    {events : Σ source : Signature, Trace source} {ordinal : Nat} {cause : Rows.Error}
    (accepted : Rows.Events.read schemaLimits limits bytes = .ok events)
    (failed : events.2.termination = .readError (.group ordinal cause)) :
    ordinal = events.2.batches.length ∧
      ∃ opened, RecursiveSchema.TwoList.openFile schemaLimits bytes = .ok opened ∧
        Rows.readGroup limits opened.schema ordinal = .error cause := by
  obtain ⟨opened, original, wire⟩ := (read_wire accepted).original
  obtain ⟨located, reached⟩ := prefix_failure wire.groups failed
  simp only [List.length_map] at located
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp located
  rw [List.getElem?_range (by simpa using bound)] at located
  exact ⟨(Option.some.inj located).symm, opened, original, reached⟩

private theorem prefix_complete {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot} {ordinals : List Nat}
    {observations : List Observation} {terminal : Arrow.Events.Termination Rows.Events.Error}
    (groups : GroupPrefix limits schema ordinals observations terminal) :
    terminal = .eos ↔ ordinals.mapM (Rows.readGroup limits schema) = .ok observations := by
  induction groups with
  | eos => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | failed original => simp [List.mapM_cons, original, bind, Except.bind]
  | @more group rest batch batches terminal original _ _ tail =>
    rw [tail]
    cases remainder : rest.mapM (Rows.readGroup limits schema) <;>
      simp [List.mapM_cons, original, remainder, bind, Except.bind, Pure.pure, Except.pure]

public theorem source_complete {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot}
    {events : Σ source : Signature, Trace source}
    (accepted : readSource limits schema = .ok events) :
    events.2.termination = .eos ↔
      Rows.readAll limits schema = .ok (events.2.batches.map eraseBatch) :=
  prefix_complete (readSource_wire accepted).groups

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events
