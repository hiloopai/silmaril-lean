module

public import Silmaril.Formats.Parquet.Reader.Recursive.Defs
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms

namespace Silmaril.Proofs.Formats.Parquet.Reader.Recursive

open Silmaril.Formats
open Parquet.Reader.Recursive
open Arrow.RecursiveSchema (Field)
open Arrow.RecursiveSchema.Batch.Rows (Observation RowFits)
open Arrow.RecursiveSchema.Stream.Events
  (Signature Value signature declarations_signature rowsOfBatch eraseBatch eraseBatch_ofBatch ofBatch)
open Silmaril.Relational (AlignedColumns)

public theorem group_error {fields : List Field} {Failure Error : Type} {report : Failure → Error}
    {result : Except Failure Observation} {cause : Failure}
    {typed : ∀ batch, result = .ok batch → ∀ row ∈ batch.rows, RowFits fields row}
    (failed : result = .error cause) : groupRows report result typed = .error (report cause) := by
  cases failed
  rfl

public theorem group_ok {fields : List Field} {Failure Error : Type} {report : Failure → Error}
    {result : Except Failure Observation} {batch : Observation}
    {typed : ∀ batch, result = .ok batch → ∀ row ∈ batch.rows, RowFits fields row}
    (accepted : result = .ok batch) :
    groupRows report result typed = .ok (rowsOfBatch fields batch (typed batch accepted)) := by
  cases accepted
  rfl

private theorem denote_wire {fields : List Field} {Group Failure Error : Type}
    (groups : Groups fields Group Failure Error) (order : List Group) :
    let observed := Parquet.Reader.denoteGroups groups.toReader.readGroup order
    Prefix groups.readGroup groups.report order
      ((observed.1.map AlignedColumns.ofRows).map eraseBatch) observed.2 := by
  induction order with
  | nil => exact .eos
  | cons group rest ih =>
    cases original : groups.readGroup group with
    | error cause =>
      have reached : groups.toReader.readGroup group = .error (groups.report group cause) :=
        group_error original
      simpa [Parquet.Reader.denoteGroups, reached] using
        (Prefix.failed (readGroup := groups.readGroup) (report := groups.report) (rest := rest) original)
    | ok batch =>
      have checked := groups.checked original
      have reached : groups.toReader.readGroup group = .ok (rowsOfBatch fields batch checked.2) :=
        group_ok original
      simp only [Parquet.Reader.denoteGroups, reached, List.map_cons]
      change Prefix groups.readGroup groups.report (group :: rest)
        (eraseBatch (ofBatch fields batch checked.2) :: _) _
      rw [eraseBatch_ofBatch _ _ _ checked.1]
      exact .more original ih

public theorem events_wire {fields : List Field} {Group Failure Error : Type}
    {groups : Groups fields Group Failure Error} {events : Σ source : Signature, Trace source Error}
    (accepted : groups.events = .ok events) : Wire groups events.1 events.2 := by
  unfold Groups.events at accepted
  rw [Parquet.Reader.readAll_opened] at accepted
  have same := Except.ok.inj accepted
  subst events
  exact ⟨declarations_signature _, denote_wire groups _⟩

public theorem prefix_failure {Group Failure Error : Type}
    {readGroup : Group → Except Failure Observation} {report : Group → Failure → Error}
    {order : List Group} {batches : List Observation} {terminal : Arrow.Events.Termination Error}
    {error : Error} (witness : Prefix readGroup report order batches terminal)
    (failed : terminal = .readError error) :
    ∃ group cause, order[batches.length]? = some group ∧
      readGroup group = .error cause ∧ report group cause = error := by
  induction witness with
  | eos => contradiction
  | failed original =>
    cases failed
    exact ⟨_, _, rfl, original, rfl⟩
  | more _ _ ih => exact ih failed

public theorem prefix_groups {Group Failure Error : Type}
    {readGroup : Group → Except Failure Observation} {report : Group → Failure → Error}
    {order : List Group} {batches : List Observation} {terminal : Arrow.Events.Termination Error}
    (witness : Prefix readGroup report order batches terminal) :
    List.Forall₂ (fun group batch => readGroup group = .ok batch) (order.take batches.length) batches := by
  induction witness with
  | eos => exact .nil
  | failed _ => exact .nil
  | more accepted _ ih => exact .cons accepted ih

public theorem prefix_complete {Group Failure Error : Type}
    {readGroup : Group → Except Failure Observation} {report : Group → Failure → Error}
    {order : List Group} {batches : List Observation} {terminal : Arrow.Events.Termination Error}
    (witness : Prefix readGroup report order batches terminal) :
    terminal = .eos ↔ order.mapM readGroup = .ok batches := by
  induction witness with
  | eos => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | failed original => simp [List.mapM_cons, original, bind, Except.bind]
  | @more group rest batch batches terminal original _ ih =>
    rw [ih]
    cases remainder : rest.mapM readGroup <;>
      simp [List.mapM_cons, original, remainder, bind, Except.bind, Pure.pure, Except.pure]

end Silmaril.Proofs.Formats.Parquet.Reader.Recursive
