module

public import Silmaril.Formats.Parquet.RecursiveSchema.Rows.Events.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Rows.Thms
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Rows.Events

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.RecursiveSchema
open Silmaril.Formats.Parquet.RecursiveSchema.Rows.Events
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation)
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events
  (Signature declarations_signature eraseBatch eraseBatch_ofBatch ofBatch rowsOfBatch)
open Silmaril.Relational (AlignedColumns)

public theorem denote_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Rows.Limits) (schema : Compiled schemaLimits snapshot) (ordinals : List Nat) :
    let observed := Reader.denoteGroups (readGroup limits schema) ordinals
    GroupPrefix limits schema ordinals
      ((observed.1.map AlignedColumns.ofRows).map eraseBatch) observed.2 := by
  induction ordinals with
  | nil => exact .eos
  | cons group rest tail =>
    cases original : Rows.readGroup limits schema group with
    | error cause =>
      have reached : readGroup limits schema group = .error (.group group cause) := by
        unfold readGroup
        split <;> simp_all
      simpa [Reader.denoteGroups, reached] using
        (GroupPrefix.failed (rest := rest) original)
    | ok batch =>
      have wire := Rows.readGroup_wire original
      have reached : readGroup limits schema group = .ok
          (rowsOfBatch schema.arrow.fields batch wire.typed) := by
        unfold readGroup
        split <;> simp_all
      simp only [Reader.denoteGroups, reached, List.map_cons]
      change GroupPrefix limits schema (group :: rest)
        (eraseBatch (ofBatch schema.arrow.fields batch wire.typed) :: _) _
      rw [eraseBatch_ofBatch _ _ _ wire.count]
      exact .more original wire tail

public theorem readSource_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Rows.Limits} {schema : Compiled schemaLimits snapshot}
    {events : Σ source : Signature, Trace source}
    (accepted : readSource limits schema = .ok events) : SourceWire limits schema events.1 events.2 := by
  unfold readSource at accepted
  rw [Reader.readAll_opened] at accepted
  have same := Except.ok.inj accepted
  subst events
  exact ⟨declarations_signature _, denote_wire limits schema _⟩

public theorem read_wire {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {bytes : Bytes}
    {events : Σ source : Signature, Trace source}
    (accepted : Rows.Events.read schemaLimits limits bytes = .ok events) :
    FileWire schemaLimits limits bytes events.1 events.2 := by
  unfold Rows.Events.read at accepted
  split at accepted
  · contradiction
  · rename_i opened original
    exact ⟨opened, original, readSource_wire accepted⟩

public theorem prefix_failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Rows.Limits} {schema : Compiled schemaLimits snapshot} {ordinals : List Nat}
    {observations : List Observation}
    {ordinal : Nat} {cause : Rows.Error}
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

public theorem prefix_eos {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Rows.Limits} {schema : Compiled schemaLimits snapshot} {ordinals : List Nat}
    {observations : List Observation}
    {terminal : Arrow.Events.Termination Rows.Events.Error}
    (groups : GroupPrefix limits schema ordinals observations terminal) (eos : terminal = .eos) :
    ordinals.mapM (Rows.readGroup limits schema) = .ok observations := by
  induction groups with
  | eos => rfl
  | failed => contradiction
  | more original _ _ tail =>
    simp only [List.mapM_cons, original, tail eos, bind, Except.bind]
    rfl

public theorem prefix_of_all {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Rows.Limits} {schema : Compiled schemaLimits snapshot} {ordinals : List Nat}
    {observations expected : List Observation}
    {terminal : Silmaril.Formats.Arrow.Events.Termination Rows.Events.Error}
    (groups : GroupPrefix limits schema ordinals observations terminal)
    (all : ordinals.mapM (Rows.readGroup limits schema) = .ok expected) :
    observations = expected ∧ terminal = .eos := by
  induction groups generalizing expected with
  | eos => exact ⟨Except.ok.inj all, rfl⟩
  | failed original => simp [List.mapM_cons, original, bind, Except.bind] at all
  | @more group rest batch batches terminal original _ _ ih =>
    cases remainder : rest.mapM (Rows.readGroup limits schema) with
    | error cause => simp [List.mapM_cons, original, remainder, bind, Except.bind] at all
    | ok values =>
      have result := ih remainder
      simp [List.mapM_cons, original, remainder, bind, Except.bind] at all
      exact ⟨(congrArg (batch :: ·) result.1).trans (Except.ok.inj all), result.2⟩

public theorem read_failure {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {bytes : Bytes}
    {events : Σ source : Signature, Trace source} {ordinal : Nat} {cause : Rows.Error}
    (accepted : Rows.Events.read schemaLimits limits bytes = .ok events)
    (failed : events.2.termination = .readError (.group ordinal cause)) :
    ordinal = events.2.batches.length ∧
      ∃ opened, openFile schemaLimits bytes = .ok opened ∧
        Rows.readGroup limits opened.schema ordinal = .error cause := by
  obtain ⟨opened, original, wire⟩ := (read_wire accepted).original
  obtain ⟨located, reached⟩ := prefix_failure wire.groups failed
  simp only [List.length_map] at located
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp located
  rw [List.getElem?_range (by simpa using bound)] at located
  exact ⟨(Option.some.inj located).symm, opened, original, reached⟩

public theorem read_eos {schemaLimits : Snapshot.Limits} {limits : Rows.Limits} {bytes : Bytes}
    {events : Σ source : Signature, Trace source}
    (accepted : Rows.Events.read schemaLimits limits bytes = .ok events)
    (eos : events.2.termination = .eos) :
    ∃ opened, openFile schemaLimits bytes = .ok opened ∧
      Rows.readAll limits opened.schema = .ok (events.2.batches.map eraseBatch) := by
  obtain ⟨opened, original, wire⟩ := (read_wire accepted).original
  exact ⟨opened, original, prefix_eos wire.groups eos⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Rows.Events
