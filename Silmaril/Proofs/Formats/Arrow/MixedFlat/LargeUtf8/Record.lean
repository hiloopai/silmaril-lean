module

public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Defs
import Silmaril.Formats.Arrow.LargeUtf8.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8

open Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.MixedFlat.LargeUtf8

private theorem groups_aligned {rows : Nat} {fields : List MixedFlat.LargeUtf8.Field}
    {groups : List (MixedFlat.Group rows)} (same : groups.map MixedFlat.Group.field = fields.map Field.layout) :
    List.Forall₂ (fun field group => group.field = field.layout) fields groups := by
  induction fields generalizing groups with
  | nil =>
    cases groups with
    | nil => exact .nil
    | cons => simp at same
  | cons field rest ih =>
    cases groups with
    | nil => simp at same
    | cons group tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      exact .cons same.1 (ih same.2)

private theorem readColumns_sound {limits : MixedFlat.Limits} {body : KBytes} {rows index : Nat}
    {groups : List (MixedFlat.LargeUtf8.Field × MixedFlat.Group rows)} {columns : List (MixedFlat.LargeUtf8.Field × MixedFlat.LargeUtf8.Column)}
    (read : readColumns limits body index groups = .ok columns) :
    List.Forall₂ (ColumnWire limits body) groups columns := by
  induction groups generalizing index columns with
  | nil =>
    simp [readColumns] at read
    subst columns
    exact .nil
  | cons pair tail ih =>
    obtain ⟨field, group⟩ := pair
    cases head : readColumn limits body field group with
    | error => simp [readColumns, head, Bind.bind, Except.bind, Except.mapError] at read
    | ok column =>
      cases rest : readColumns limits body (index + 1) tail with
      | error => simp [readColumns, head, rest, Bind.bind, Except.bind, Except.mapError] at read
      | ok observed =>
        simp [readColumns, head, rest, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] at read
        subst columns
        exact .cons ⟨rfl, head⟩ (ih rest)

theorem readParsed_sound {limits : MixedFlat.Limits} {fields : List MixedFlat.LargeUtf8.Field}
    {metadata : MixedFlat.Metadata} {body : KBytes} {observed : Observed}
    (read : readParsed limits fields metadata body = .ok observed) :
    BatchWire limits fields metadata body observed := by
  cases checked : MixedFlat.bindBatch limits (fields.map Field.layout) metadata body with
  | error => simp [readParsed, checked, Bind.bind, Except.bind, Except.mapError] at read
  | ok plan =>
    cases decoded : readColumns limits body 0 (fields.zip plan.assignment.groups) with
    | error => simp [readParsed, checked, decoded, Bind.bind, Except.bind, Except.mapError] at read
    | ok columns =>
      simp [readParsed, checked, decoded, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] at read
      subst observed
      exact ⟨plan, checked, rfl, groups_aligned plan.assignment.fieldsExact, readColumns_sound decoded⟩

theorem readBatch_sound {limits : MixedFlat.Limits} {schemaBytes recordBytes body : KBytes}
    {observed : Observed} (read : readBatch limits schemaBytes recordBytes body = .ok observed) :
    ∃ fields metadata, readSchema limits.observation.ipc schemaBytes = .ok fields ∧
      readMetadata limits fields recordBytes = .ok metadata ∧ BatchWire limits fields metadata body observed := by
  cases schema : readSchema limits.observation.ipc schemaBytes with
  | error => simp [readBatch, schema, Bind.bind, Except.bind, Except.mapError] at read
  | ok fields =>
    cases metadata : readMetadata limits fields recordBytes with
    | error => simp [readBatch, schema, metadata, Bind.bind, Except.bind, Except.mapError] at read
    | ok record =>
      exact ⟨fields, record, rfl, metadata,
        readParsed_sound (by simpa [readBatch, schema, metadata, Bind.bind, Except.bind, Except.mapError] using read)⟩

private theorem column_fields {limits : MixedFlat.Limits} {body : KBytes} {rows : Nat}
    {groups : List (MixedFlat.LargeUtf8.Field × MixedFlat.Group rows)} {columns : List (MixedFlat.LargeUtf8.Field × MixedFlat.LargeUtf8.Column)}
    (wire : List.Forall₂ (ColumnWire limits body) groups columns) :
    columns.map Prod.fst = groups.map Prod.fst := by
  induction wire with
  | nil => rfl
  | cons head _ ih => simp [head.1, ih]

theorem batch_fields {limits : MixedFlat.Limits} {fields : List MixedFlat.LargeUtf8.Field}
    {metadata : MixedFlat.Metadata} {body : KBytes} {observed : Observed}
    (wire : BatchWire limits fields metadata body observed) :
    observed.rowCount = metadata.batch.rowCount ∧ observed.columns.map Prod.fst = fields := by
  obtain ⟨plan, _, rows, aligned, columns⟩ := wire.bound
  exact ⟨rows, (column_fields columns).trans (List.map_fst_zip (Nat.le_of_eq aligned.length_eq))⟩

theorem largeUtf8_column {limits : MixedFlat.Limits} {body : KBytes} {field : MixedFlat.LargeUtf8.Field} {rows : Nat}
    {group : MixedFlat.Group rows} {values : Arrow.LargeUtf8.Column}
    (kind : field.kind = .largeUtf8)
    (read : readColumn limits body field group = .ok (.largeUtf8 values)) :
    ∃ validity offsets data,
      group.buffers = [validity, offsets, data] ∧
      let buffers : Binary.Buffers :=
        ⟨Body.sliceBuffer body validity, Body.sliceBuffer body offsets, Body.sliceBuffer body data⟩
      Binary.checkColumn limits.observation.ipc field.nullable group.node buffers = .ok () ∧
      Arrow.LargeUtf8.ColumnWire group.node buffers values := by
  simp only [readColumn, kind] at read
  split at read
  next validity offsets data layout =>
    let buffers : Binary.Buffers :=
      ⟨Body.sliceBuffer body validity, Body.sliceBuffer body offsets, Body.sliceBuffer body data⟩
    cases physical : Arrow.LargeUtf8.readColumn limits.observation.ipc field.nullable group.node buffers with
    | error =>
      simp [buffers] at physical
      simp [physical, Except.mapError, Except.map] at read
    | ok actual =>
      have decoded : actual = values := by
        simp [buffers] at physical
        simpa [physical, Except.mapError, Except.map] using read
      subst actual
      exact ⟨validity, offsets, data, layout, Arrow.LargeUtf8.readColumn_sound physical⟩
  next => cases read

end Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8
