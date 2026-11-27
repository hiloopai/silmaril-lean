module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedTimestamp.Defs
import Silmaril.Formats.Csv.Typed.Thms
import Silmaril.Semantics.Relational.Scan.Thms

public section

namespace Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp

open Silmaril.Formats Silmaril.Relational
open Csv.Typed.Utf8.MixedTimestamp
open Arrow.MixedFlat.Timestamp (Batch)

private theorem columnCells_packColumn (field : Field) (values : List (Option (Cell field))) :
    columnCells field (packColumn field values) = some values := by
  obtain ⟨name, nullable, kind⟩ := field
  cases kind with
  | int32 | utf8 => rfl
  | timestamp metadata =>
    change some ((values.map (Option.map (·.ticks))).map (Option.map fun ticks => ⟨ticks⟩)) = some values
    congr 1
    calc
      _ = values.map id := by
        rw [List.map_map]
        apply List.map_congr_left
        intro value _
        cases value with
        | none => rfl
        | some tick => cases tick; rfl
      _ = values := List.map_id values

theorem flatten_streamOfRows (fields : List Field)
    (rows : Csv.Typed.Table (schemaOf fields) Cell) :
    flatten fields (streamOfRows fields rows).batches = .ok rows := by
  let aligned : Scan.Columns (schemaOf fields) Cell := AlignedColumns.ofRows rows
  let batch : Batch := ⟨rows.length, List.ofFn fun i => packColumn (fields.get i) (aligned.values i)⟩
  have same : batch.columns.length = fields.length := by simp [batch]
  let columns : (i : Fin fields.length) → { values : List (Option (Cell (fields.get i))) //
      values.length = rows.length } :=
    fun i => ⟨aligned.values i, aligned.length_eq i⟩
  have checked : Csv.Typed.Internal.collect (columnAt fields batch 0 same) = .ok columns := by
    apply (Csv.Typed.collect_ok _ _).mpr
    intro i
    have sized : (aligned.values i).length = rows.length := aligned.length_eq i
    simp [columnAt, batch, columnCells_packColumn, sized, columns, pure, Except.pure]
  have unpacked : batchRows fields batch 0 = .ok rows := by
    simp only [batchRows, same, ↓reduceDIte, checked, Bind.bind, Except.bind, pure, Except.pure]
    change Except.ok aligned.toRows = Except.ok rows
    simp [aligned]
  change flatten fields [batch] = .ok rows
  simp [flatten, unpacked, Bind.bind, Except.bind, Except.map, pure, Except.pure]

end Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp
