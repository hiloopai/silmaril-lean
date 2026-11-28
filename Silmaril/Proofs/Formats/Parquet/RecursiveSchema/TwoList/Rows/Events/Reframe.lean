module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Thms
import Silmaril.Formats.Parquet.Reader.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events (Signature Value signature)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Observation RowFits)

private theorem groupRows_congr {left right : List Arrow.RecursiveSchema.Field} {group : Nat}
    {before after : Except Rows.Error Observation}
    {beforeTyped : ∀ batch, before = .ok batch → ∀ row ∈ batch.rows, RowFits left row}
    {afterTyped : ∀ batch, after = .ok batch → ∀ row ∈ batch.rows, RowFits right row}
    (fields : left = right) (same : before = after) :
    HEq (groupRows left group before beforeTyped) (groupRows right group after afterTyped) := by
  cases fields
  cases same
  rfl

private theorem denote_congr {source : Signature}
    {before after : Nat → Except Rows.Events.Error (Reader.RowGroup source Value)}
    {indices : List Nat} (same : ∀ index ∈ indices, before index = after index) :
    Reader.denoteGroups before indices = Reader.denoteGroups after indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [Reader.denoteGroups, same index (by simp), ih (fun i hi => same i (by simp [hi]))]

private theorem readAll_congr {left right : Signature}
    {before : Reader.Source Nat left Value Rows.Events.Error}
    {after : Reader.Source Nat right Value Rows.Events.Error}
    (fields : left = right) (indices : before.groups = after.groups)
    (same : ∀ index ∈ before.groups, HEq (before.readGroup index) (after.readGroup index)) :
    Reader.readAll (.ok ⟨left, before⟩) = Reader.readAll (.ok ⟨right, after⟩) := by
  cases fields
  have denotation : Reader.denoteGroups before.readGroup before.groups =
      Reader.denoteGroups after.readGroup after.groups := by
    rw [← indices]
    exact denote_congr (fun index member => eq_of_heq (same index member))
  rw [Reader.readAll_opened, Reader.readAll_opened, denotation]

private theorem rows_reframe {leftSchemaLimits rightSchemaLimits : Snapshot.Limits}
    {leftSnapshot rightSnapshot : Snapshot.Checked}
    {leftLimits rightLimits : Chunk.Limits}
    {left : Compiled leftSchemaLimits leftSnapshot} {right : Compiled rightSchemaLimits rightSnapshot}
    (comparison : Reframe leftLimits left rightLimits right)
    {group : Nat} (member : group ∈ List.range leftSnapshot.groupCount) :
    Rows.readGroup leftLimits left group = Rows.readGroup rightLimits right group := by
  obtain ⟨_, _, _, _, leftBind, rightBind, leftRead, rightRead, trace⟩ := comparison.groups group member
  have same := Rows.reconstructObservation_reframe (plan := right.plan)
    (Chunk.read_wire leftRead) (Chunk.read_wire rightRead) trace
  simpa [Rows.readGroup, leftBind, rightBind, leftRead, rightRead, comparison.plan, Except.mapError,
    bind, Except.bind] using same

public theorem reframe {leftSchemaLimits rightSchemaLimits : Snapshot.Limits}
    {leftSnapshot rightSnapshot : Snapshot.Checked}
    {leftLimits rightLimits : Chunk.Limits}
    {left : Compiled leftSchemaLimits leftSnapshot} {right : Compiled rightSchemaLimits rightSnapshot}
    (comparison : Reframe leftLimits left rightLimits right) :
    readSource leftLimits left = readSource rightLimits right := by
  have fields := congrArg (fun plan => (Rows.arrowSchema plan).fields) comparison.plan
  unfold readSource
  apply readAll_congr (congrArg signature fields) (congrArg List.range comparison.count)
  intro index member
  exact groupRows_congr fields (rows_reframe comparison member)

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events
