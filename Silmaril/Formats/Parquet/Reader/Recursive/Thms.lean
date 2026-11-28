module

public import Silmaril.Formats.Parquet.Reader.Recursive.Defs
import Silmaril.Proofs.Formats.Parquet.Reader.Recursive.Prefix
import Silmaril.Proofs.Formats.Parquet.Reader.Recursive.Agreement

namespace Silmaril.Formats.Parquet.Reader.Recursive

open Arrow.RecursiveSchema (Field)
open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Arrow.RecursiveSchema.Stream.Events (Signature)

public section

theorem Groups.events_wire {fields : List Field} {Group Failure Error : Type}
    {groups : Groups fields Group Failure Error} {events : Σ source : Signature, Trace source Error}
    (accepted : groups.events = .ok events) : Wire groups events.1 events.2 :=
  Proofs.Formats.Parquet.Reader.Recursive.events_wire accepted

theorem Prefix.failure {Group Failure Error : Type}
    {readGroup : Group → Except Failure Observation} {report : Group → Failure → Error}
    {order : List Group} {batches : List Observation} {terminal : Arrow.Events.Termination Error}
    {error : Error} (witness : Prefix readGroup report order batches terminal)
    (failed : terminal = .readError error) :
    ∃ group cause, order[batches.length]? = some group ∧
      readGroup group = .error cause ∧ report group cause = error :=
  Proofs.Formats.Parquet.Reader.Recursive.prefix_failure witness failed

theorem Prefix.groups {Group Failure Error : Type}
    {readGroup : Group → Except Failure Observation} {report : Group → Failure → Error}
    {order : List Group} {batches : List Observation} {terminal : Arrow.Events.Termination Error}
    (witness : Prefix readGroup report order batches terminal) :
    List.Forall₂ (fun group batch => readGroup group = .ok batch) (order.take batches.length) batches :=
  Proofs.Formats.Parquet.Reader.Recursive.prefix_groups witness

theorem Prefix.complete {Group Failure Error : Type}
    {readGroup : Group → Except Failure Observation} {report : Group → Failure → Error}
    {order : List Group} {batches : List Observation} {terminal : Arrow.Events.Termination Error}
    (witness : Prefix readGroup report order batches terminal) :
    terminal = .eos ↔ order.mapM readGroup = .ok batches :=
  Proofs.Formats.Parquet.Reader.Recursive.prefix_complete witness

theorem Groups.events_eq_of_complete {Group Failure Error : Type} {leftFields rightFields : List Field}
    {left : Groups leftFields Group Failure Error} {right : Groups rightFields Group Failure Error}
    {batches : List Observation} (fields : leftFields = rightFields) (order : left.order = right.order)
    (before : left.order.mapM left.readGroup = .ok batches)
    (after : right.order.mapM right.readGroup = .ok batches) :
    left.events = right.events :=
  Proofs.Formats.Parquet.Reader.Recursive.events_eq_of_complete fields order before after

end

end Silmaril.Formats.Parquet.Reader.Recursive
