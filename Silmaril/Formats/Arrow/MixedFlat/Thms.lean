module

public import Silmaril.Formats.Arrow.MixedFlat.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Assignment

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat

/-- Assignment exhausts every field, node, view count and descriptor,
preserving each input order. -/
theorem Assignment.exact {rows : Nat} {fields : List Field} {nodes : List FieldNode}
    {counts : List Nat} {buffers : List Buffer} (assignment : Assignment rows fields nodes counts buffers) :
    assignment.groups.map Group.field = fields ∧ assignment.groups.map Group.node = nodes ∧
    assignment.groups.filterMap Group.count = counts ∧ assignment.groups.flatMap Group.buffers = buffers :=
  ⟨assignment.fieldsExact, assignment.nodesExact, assignment.countsExact, assignment.buffersExact⟩

/-- Each field is tied to the common row count. View counts occupy exactly the
view groups, and each group has its declared physical width. -/
theorem Group.shape {rows : Nat} (group : Group rows) :
    group.node.length = rows ∧ group.count.isSome = group.field.kind.isView ∧
    group.buffers.length = group.field.kind.baseBuffers + group.count.getD 0 :=
  ⟨group.rowsExact, group.countKind, group.width⟩

/-- Distinct descriptor positions use ordered non-overlapping body extents,
including positions on either side of a column boundary. -/
theorem Plan.ordered_disjoint {fields : List Field} {metadata : Metadata} {body : KBytes}
    (plan : Plan fields metadata body) {before between after : List Buffer} {first second : Buffer}
    (split : plan.assignment.groups.flatMap Group.buffers = before ++ first :: between ++ second :: after) :
    first.offset + first.length ≤ second.offset :=
  Proofs.Formats.Arrow.MixedFlat.ordered_disjoint plan split

/-- Every assigned descriptor selects its exact bounded byte window. -/
theorem Plan.buffer_exact {fields : List Field} {metadata : Metadata} {body : KBytes}
    (plan : Plan fields metadata body) {group : Group metadata.batch.rowCount}
    (assigned : group ∈ plan.assignment.groups) {buffer : Buffer} (member : buffer ∈ group.buffers) :
    (Body.sliceBuffer body buffer).len = buffer.length ∧
    (Body.sliceBuffer body buffer).toList = (body.toList.drop buffer.offset).take buffer.length :=
  Proofs.Formats.Arrow.MixedFlat.buffer_exact plan assigned member

/-- Decoding a checked plan preserves exactly its declared field order. -/
theorem Plan.readGroups_fields {fields : List Field} {metadata : Metadata} {body : KBytes}
    (plan : Plan fields metadata body) {limits : BinaryView.Column.Limits}
    {columns : List (Field × Column)}
    (read : readGroups limits body 0 plan.assignment.groups = .ok columns) :
    columns.map Prod.fst = fields :=
  (Proofs.Formats.Arrow.MixedFlat.readGroups_fields read).trans plan.assignment.fieldsExact

/-- Once layout binding succeeds, a column rejection retains its field index. -/
theorem readGroups_error_field {limits : BinaryView.Column.Limits} {body : KBytes}
    {rows index : Nat} {groups : List (Group rows)} {cause : Error}
    (failed : readGroups limits body index groups = .error cause) :
    ∃ field error, cause = .field field error :=
  Proofs.Formats.Arrow.MixedFlat.readGroups_error_field failed

/-- A successful mixed read preserves the exact checked Schema field order
and the declared RecordBatch row count. -/
theorem readBatch_shape {limits : Limits} {schema bytes body : KBytes} {result : Observed}
    (read : readBatch limits schema bytes body = .ok result) :
    ∃ fields metadata,
      readSchema limits.observation.ipc schema = .ok fields ∧
      readMetadata limits.observation.ipc limits.view.dataBuffers limits.totalDataBuffers fields bytes =
        .ok metadata ∧
      result.rowCount = metadata.batch.rowCount ∧ result.columns.map Prod.fst = fields :=
  Proofs.Formats.Arrow.MixedFlat.readBatch_shape read

end Silmaril.Formats.Arrow.MixedFlat
