module

public import Silmaril.Formats.Arrow.MixedFlat.Events.Defs
import Silmaril.Formats.Arrow.MixedFlat.Thms
import Silmaril.Formats.Arrow.Body.Thms
import Silmaril.Formats.Arrow.BinaryView.Column.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Events

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational
open MixedFlat MixedFlat.Events

/-- Number of nullable slots in a decoded mixed column. -/
private def slotCount : MixedFlat.Column → Nat
  | .primitive values => values.length
  | .binaryView values => values.length
  | .utf8View values => values.length

private theorem cellsLength {buffers : Body.ColumnBuffers} {indices : List Nat}
    {values : Arrow.Column} (wire : Body.CellsWire buffers indices values) :
    values.length = indices.length := by
  induction indices generalizing values with
  | nil => cases values <;> simp_all [Body.CellsWire]
  | cons index indices ih =>
    cases values with
    | nil => exact wire.elim
    | cons value values => exact congrArg Nat.succ (ih wire.2)

private theorem groupSlots {limits : BinaryView.Column.Limits} {body : KBytes} {rows : Nat}
    {group : Group rows} {column : MixedFlat.Column}
    (read : readGroup limits body group = .ok column) : slotCount column = rows := by
  unfold readGroup at read
  split at read
  · rename_i kind _
    split at read <;> try contradiction
    rename_i buffers _
    cases decoded : Body.readColumn group.node buffers with
    | error => simp [decoded, bind, Except.bind, Except.mapError] at read
    | ok values =>
      simp [decoded, bind, Except.bind, Except.mapError, pure, Except.pure] at read
      subst column
      have wire := (Body.readColumn_iff group.node buffers values).mp decoded
      simpa [slotCount, group.rowsExact] using cellsLength wire.2.2.1
  · rename_i kind _
    split at read <;> try contradiction
    split at read
    · rename_i validity views data _ _ _
      let buffers : BinaryView.Column.Buffers := ⟨Body.sliceBuffer body validity,
        ⟨Body.sliceBuffer body views, data.toArray.map (Body.sliceBuffer body)⟩⟩
      change (do
        let values ← (BinaryView.Column.readBinary limits group.node group.field.nullable buffers).mapError ColumnError.view
        pure (MixedFlat.Column.binaryView values)) = .ok column at read
      cases decoded : BinaryView.Column.readBinary limits group.node group.field.nullable buffers with
      | error => simp only [decoded, bind, Except.bind, Except.mapError, reduceCtorEq] at read
      | ok values =>
        simp only [decoded, bind, Except.bind, Except.mapError, pure, Except.pure, Except.ok.injEq] at read
        subst column
        exact (BinaryView.Column.readBinary_bounds decoded).2.1.trans group.rowsExact
    · rename_i validity views data _ _ _
      let buffers : BinaryView.Column.Buffers := ⟨Body.sliceBuffer body validity,
        ⟨Body.sliceBuffer body views, data.toArray.map (Body.sliceBuffer body)⟩⟩
      change (do
        let values ← (BinaryView.Column.readUtf8 limits group.node group.field.nullable buffers).mapError ColumnError.view
        pure (MixedFlat.Column.utf8View values)) = .ok column at read
      cases decoded : BinaryView.Column.readUtf8 limits group.node group.field.nullable buffers with
      | error => simp only [decoded, bind, Except.bind, Except.mapError, reduceCtorEq] at read
      | ok values =>
        simp only [decoded, bind, Except.bind, Except.mapError, pure, Except.pure, Except.ok.injEq] at read
        subst column
        exact (BinaryView.Column.readUtf8_counts decoded).1.trans group.rowsExact

theorem readGroup_length {limits : BinaryView.Column.Limits} {body : KBytes} {rows : Nat}
    {group : Group rows} {column : MixedFlat.Column}
    (read : readGroup limits body group = .ok column) : (cells column).length = rows := by
  have length := groupSlots read
  cases column <;> simpa [cells, slotCount] using length

private theorem groupListSlots {limits : BinaryView.Column.Limits} {body : KBytes} {rows : Nat}
    {groups : List (Group rows)} {index : Nat} {columns : List (MixedFlat.Field × MixedFlat.Column)}
    (read : readGroups limits body index groups = .ok columns) :
    ∀ pair ∈ columns, slotCount pair.2 = rows := by
  induction groups generalizing index columns with
  | nil =>
    simp [readGroups] at read
    subst columns
    simp
  | cons group rest ih =>
    cases head : readGroup limits body group with
    | error => simp [readGroups, head, bind, Except.bind, Except.mapError] at read
    | ok value =>
      cases tail : readGroups limits body (index + 1) rest with
      | error => simp [readGroups, head, tail, bind, Except.bind, Except.mapError] at read
      | ok values =>
        simp [readGroups, head, tail, bind, Except.bind, Except.mapError, pure, Except.pure] at read
        subst columns
        intro pair member
        rcases List.mem_cons.mp member with rfl | member
        · exact groupSlots head
        · exact ih tail pair member

theorem readParsed_shape {limits : MixedFlat.Limits} {body : KBytes}
    {fields : List MixedFlat.Field} {metadata : MixedFlat.Metadata} {observed : MixedFlat.Observed}
    (parsed : MixedFlat.readParsed limits fields metadata body = .ok observed) :
    observed.columns.map Prod.fst = fields ∧
      ∀ pair ∈ observed.columns, (cells pair.2).length = observed.rowCount := by
  unfold readParsed at parsed
  cases bound : bindBatch limits fields metadata body with
  | error => simp [bound, bind, Except.bind] at parsed
  | ok plan =>
    cases groups : readGroups limits.view body 0 plan.assignment.groups with
    | error => simp [bound, groups, bind, Except.bind] at parsed
    | ok columns =>
      simp [bound, groups, bind, Except.bind, pure, Except.pure] at parsed
      subst observed
      refine ⟨plan.readGroups_fields groups, fun pair member => ?_⟩
      have slots := groupListSlots groups pair member
      cases column : pair.2 <;> simpa [column, cells, slotCount] using slots

theorem ofObserved_agrees (fields : List MixedFlat.Field) (observed : MixedFlat.Observed)
    (ordered : observed.columns.map Prod.fst = fields)
    (aligned : ∀ pair ∈ observed.columns, (cells pair.2).length = observed.rowCount) :
    Agrees (schema fields) observed (ofObserved fields observed ordered aligned) := by
  have width : observed.columns.length = fields.length := by
    simpa using congrArg List.length ordered
  refine ⟨rfl, width, fun i => ?_⟩
  have bound : i.val < observed.columns.length := Nat.lt_of_lt_of_eq i.isLt width.symm
  have label := congrArg (fun values : List MixedFlat.Field => values[i.val]?) ordered
  simp only [List.getElem?_map, List.getElem?_eq_getElem bound,
    List.getElem?_eq_getElem (show i.val < fields.length from i.isLt), Option.map_some,
    Option.some.injEq] at label
  rw [List.getElem?_eq_getElem bound]
  simp [ofObserved, schema, label]

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Events
