module

public import Silmaril.Formats.Arrow.MixedFlat.Defs
import Silmaril.Formats.Arrow.Layout.Thms
import Silmaril.Prelude.Bytes.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat

open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.MixedFlat

private theorem ordered_pair {length prior : Nat} (before : List Buffer)
    {first second : Buffer} {between after : List Buffer}
    (fit : BuffersFit length prior (before ++ first :: between ++ second :: after)) :
    first.offset + first.length ≤ second.offset := by
  induction before generalizing prior with
  | nil =>
    have tail : BuffersFit length (first.offset + first.length) (between ++ second :: after) := fit.2
    exact (tail.mem_fits (by simp)).1
  | cons head rest ih => exact ih fit.2

theorem ordered_disjoint {fields : List MixedFlat.Field} {metadata : Metadata} {body : KBytes}
    (plan : Plan fields metadata body) {before between after : List Buffer} {first second : Buffer}
    (split : plan.assignment.groups.flatMap Group.buffers = before ++ first :: between ++ second :: after) :
    first.offset + first.length ≤ second.offset := by
  have fit := plan.ordered
  rw [← plan.assignment.buffersExact, split] at fit
  exact ordered_pair before fit

theorem buffer_exact {fields : List MixedFlat.Field} {metadata : Metadata} {body : KBytes}
    (plan : Plan fields metadata body) {group : Group metadata.batch.rowCount}
    (assigned : group ∈ plan.assignment.groups) {buffer : Buffer} (member : buffer ∈ group.buffers) :
    (Body.sliceBuffer body buffer).len = buffer.length ∧
    (Body.sliceBuffer body buffer).toList = (body.toList.drop buffer.offset).take buffer.length := by
  have wireMember : buffer ∈ metadata.batch.buffers := by
    rw [← plan.assignment.buffersExact]
    exact List.mem_flatMap.mpr ⟨group, assigned, member⟩
  have fit := plan.ordered.mem_fits wireMember
  exact ⟨KBytes.len_slice _ _ _, KBytes.toList_slice _ _ _ plan.source fit.2.2⟩

theorem readGroups_fields {limits : BinaryView.Column.Limits} {body : KBytes} {rows index : Nat}
    {groups : List (Group rows)} {columns : List (MixedFlat.Field × MixedFlat.Column)}
    (read : readGroups limits body index groups = .ok columns) :
    columns.map Prod.fst = groups.map Group.field := by
  induction groups generalizing index columns with
  | nil => simp [readGroups] at read; subst columns; rfl
  | cons group groups ih =>
    cases head : readGroup limits body group with
    | error => simp [readGroups, head, Except.bind, Except.mapError, bind] at read
    | ok column =>
      cases tail : readGroups limits body (index + 1) groups with
      | error => simp [readGroups, head, tail, Except.bind, Except.mapError, bind] at read
      | ok values =>
        have same : (group.field, column) :: values = columns := by
          simpa [readGroups, head, tail, Except.bind, Except.mapError, bind, pure, Except.pure] using read
        subst columns
        simp [ih tail]

theorem readGroups_error_field {limits : BinaryView.Column.Limits} {body : KBytes}
    {rows index : Nat} {groups : List (Group rows)} {cause : MixedFlat.Error}
    (failed : readGroups limits body index groups = .error cause) :
    ∃ field error, cause = .field field error := by
  induction groups generalizing index cause with
  | nil => simp [readGroups] at failed
  | cons group rest ih =>
    cases column : readGroup limits body group with
    | error fault =>
      simp [readGroups, column, bind, Except.bind, Except.mapError] at failed
      exact ⟨index, fault, failed.symm⟩
    | ok values =>
      cases next : readGroups limits body (index + 1) rest with
      | error fault =>
        simp [readGroups, column, next, bind, Except.bind, Except.mapError] at failed
        subst cause
        exact ih next
      | ok columns =>
        simp [readGroups, column, next, bind, Except.bind, Except.mapError, pure, Except.pure] at failed

theorem readBatch_shape {limits : MixedFlat.Limits} {schema bytes body : KBytes} {result : Observed}
    (read : readBatch limits schema bytes body = .ok result) :
    ∃ fields metadata,
      readSchema limits.observation.ipc schema = .ok fields ∧
      readMetadata limits.observation.ipc limits.view.dataBuffers limits.totalDataBuffers fields bytes =
        .ok metadata ∧
      result.rowCount = metadata.batch.rowCount ∧ result.columns.map Prod.fst = fields := by
  cases schemaRead : readSchema limits.observation.ipc schema with
  | error => simp [readBatch, schemaRead, bind, Except.bind, Except.mapError] at read
  | ok fields =>
    cases metadataRead : readMetadata limits.observation.ipc limits.view.dataBuffers
        limits.totalDataBuffers fields bytes with
    | error => simp [readBatch, schemaRead, metadataRead, bind, Except.bind, Except.mapError] at read
    | ok metadata =>
      cases bound : bindBatch limits fields metadata body with
      | error => simp [readBatch, schemaRead, metadataRead, readParsed, bound, bind, Except.bind, Except.mapError] at read
      | ok plan =>
        cases columns : readGroups limits.view body 0 plan.assignment.groups with
        | error =>
          simp [readBatch, schemaRead, metadataRead, readParsed, bound, columns, bind, Except.bind, Except.mapError] at read
        | ok values =>
          have same : Observed.mk metadata.batch.rowCount values = result := by
            simpa [readBatch, schemaRead, metadataRead, readParsed, bound, columns, bind, Except.bind,
              Except.mapError, pure, Except.pure] using read
          subst result
          exact ⟨fields, metadata, rfl, metadataRead, rfl,
            (readGroups_fields columns).trans plan.assignment.fieldsExact⟩

end Silmaril.Proofs.Formats.Arrow.MixedFlat
