module

public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Events.Defs
import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Thms
import Silmaril.Formats.Arrow.MixedFlat.Events.Thms
import Silmaril.Formats.Arrow.LargeUtf8.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Events

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational
open MixedFlat.LargeUtf8.Events

private theorem column_length {limits : MixedFlat.Limits} {body : KBytes}
    {field : MixedFlat.LargeUtf8.Field} {rows : Nat} {group : MixedFlat.Group rows}
    {column : MixedFlat.LargeUtf8.Column}
    (read : MixedFlat.LargeUtf8.readColumn limits body field group = .ok column) :
    (cells field.kind column).length = rows := by
  cases kind : field.kind with
  | existing existing =>
    cases decoded : MixedFlat.readGroup limits.view body group with
    | error => simp [MixedFlat.LargeUtf8.readColumn, kind, decoded, Except.mapError, Except.map] at read
    | ok values =>
      simp [MixedFlat.LargeUtf8.readColumn, kind, decoded, Except.mapError, Except.map] at read
      subst column
      exact MixedFlat.Events.readGroup_length decoded
  | largeUtf8 =>
    simp only [MixedFlat.LargeUtf8.readColumn, kind] at read
    split at read
    next validity offsets data _ =>
      let buffers : Binary.Buffers :=
        ⟨Body.sliceBuffer body validity, Body.sliceBuffer body offsets, Body.sliceBuffer body data⟩
      change ((Arrow.LargeUtf8.readColumn limits.observation.ipc field.nullable group.node buffers).mapError
        MixedFlat.LargeUtf8.ColumnError.largeUtf8).map MixedFlat.LargeUtf8.Column.largeUtf8 = .ok column at read
      cases decoded : Arrow.LargeUtf8.readColumn limits.observation.ipc field.nullable group.node buffers with
      | error =>
        rw [decoded] at read
        cases read
      | ok values =>
        rw [decoded] at read
        cases read
        have slots : List.Forall₂ (Arrow.LargeUtf8.SlotWire buffers) (List.range group.node.length) values :=
          (Arrow.LargeUtf8.readColumn_sound decoded).2.2.1
        have len : values.length = group.node.length := by
          simpa only [List.length_range] using slots.length_eq.symm
        exact len.trans group.rowsExact
    next => cases read

private theorem columns_length {limits : MixedFlat.Limits} {body : KBytes} {rows : Nat}
    {assigned : List (MixedFlat.LargeUtf8.Field × MixedFlat.Group rows)}
    {columns : List (MixedFlat.LargeUtf8.Field × MixedFlat.LargeUtf8.Column)}
    (wire : List.Forall₂ (MixedFlat.LargeUtf8.ColumnWire limits body) assigned columns) :
    ∀ pair ∈ columns, (cells pair.1.kind pair.2).length = rows := by
  induction wire with
  | nil => simp
  | cons head _ ih =>
    intro pair member
    rcases List.mem_cons.mp member with rfl | member
    · rw [head.1]
      exact column_length head.2
    · exact ih pair member

theorem batch_shape {limits : MixedFlat.Limits} {body : KBytes}
    {fields : List MixedFlat.LargeUtf8.Field} {metadata : MixedFlat.Metadata}
    {observed : MixedFlat.LargeUtf8.Observed}
    (wire : MixedFlat.LargeUtf8.BatchWire limits fields metadata body observed) :
    observed.columns.map Prod.fst = fields ∧
      ∀ pair ∈ observed.columns, (cells pair.1.kind pair.2).length = observed.rowCount := by
  obtain ⟨_, names⟩ := wire.fields
  obtain ⟨_, _, rows, _, columns⟩ := wire.bound
  exact ⟨names, fun pair member => (columns_length columns pair member).trans rows.symm⟩

theorem ofObserved_agrees (fields : List MixedFlat.LargeUtf8.Field) (observed : MixedFlat.LargeUtf8.Observed)
    (ordered : observed.columns.map Prod.fst = fields)
    (aligned : ∀ pair ∈ observed.columns, (cells pair.1.kind pair.2).length = observed.rowCount) :
    Agrees (schema fields) observed (ofObserved fields observed ordered aligned) := by
  have width : observed.columns.length = fields.length := by
    simpa using congrArg List.length ordered
  refine ⟨rfl, width, fun i => ?_⟩
  have bound : i.val < observed.columns.length := Nat.lt_of_lt_of_eq i.isLt width.symm
  have label := congrArg (fun fs : List MixedFlat.LargeUtf8.Field => fs[i.val]?) ordered
  simp only [List.getElem?_map, List.getElem?_eq_getElem bound,
    List.getElem?_eq_getElem (show i.val < fields.length from i.isLt), Option.map_some,
    Option.some.injEq] at label
  refine ⟨observed.columns[i.val].2, ?_, rfl⟩
  rw [List.getElem?_eq_getElem bound]
  simp [schema, ← label]

end Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Events
