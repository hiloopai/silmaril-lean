module

public import Silmaril.Formats.Parquet.Reader.Recursive.Defs
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Proofs.Formats.Parquet.Reader.Recursive.Prefix

namespace Silmaril.Proofs.Formats.Parquet.Reader.Recursive

open Silmaril.Formats
open Parquet.Reader.Recursive
open Arrow.RecursiveSchema (Field)
open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Arrow.RecursiveSchema.Stream.Events (rowsOfBatch)

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {out : β}
    (read : (first >>= next) = .ok out) : ∃ found, first = .ok found ∧ next found = .ok out := by
  cases first with
  | error => contradiction
  | ok result => exact ⟨result, rfl, read⟩

private theorem sameDenotation {Group Failure Error : Type} {fields : List Field}
    (left right : Groups fields Group Failure Error) {order : List Group} {batches : List Observation}
    (before : order.mapM left.readGroup = .ok batches)
    (after : order.mapM right.readGroup = .ok batches) :
    Parquet.Reader.denoteGroups left.toReader.readGroup order =
      Parquet.Reader.denoteGroups right.toReader.readGroup order := by
  induction order generalizing batches with
  | nil => rfl
  | cons group rest ih =>
    simp only [List.mapM_cons] at before after
    obtain ⟨l, readL, before⟩ := bind_ok before
    obtain ⟨r, readR, after⟩ := bind_ok after
    obtain ⟨ls, tailL, doneL⟩ := bind_ok before
    obtain ⟨rs, tailR, doneR⟩ := bind_ok after
    have shared : l :: ls = r :: rs := (Except.ok.inj doneL).trans (Except.ok.inj doneR).symm
    obtain ⟨same, tails⟩ := List.cons.inj shared
    subst r
    subst rs
    have reachedL : left.toReader.readGroup group = .ok (rowsOfBatch fields l (left.checked readL).2) :=
      group_ok readL
    have reachedR : right.toReader.readGroup group = .ok (rowsOfBatch fields l (right.checked readR).2) :=
      group_ok readR
    rw [Parquet.Reader.denoteGroups, Parquet.Reader.denoteGroups, reachedL, reachedR, ih tailL tailR]

public theorem events_eq_of_complete {Group Failure Error : Type} {leftFields rightFields : List Field}
    {left : Groups leftFields Group Failure Error} {right : Groups rightFields Group Failure Error}
    {batches : List Observation} (fields : leftFields = rightFields) (order : left.order = right.order)
    (before : left.order.mapM left.readGroup = .ok batches)
    (after : right.order.mapM right.readGroup = .ok batches) :
    left.events = right.events := by
  cases fields
  unfold Groups.events
  rw [Parquet.Reader.readAll_opened, Parquet.Reader.readAll_opened]
  rw [show left.toReader.groups = right.toReader.groups from order]
  rw [show right.toReader.groups = right.order from rfl]
  rw [sameDenotation left right (order ▸ before) after]

end Silmaril.Proofs.Formats.Parquet.Reader.Recursive
