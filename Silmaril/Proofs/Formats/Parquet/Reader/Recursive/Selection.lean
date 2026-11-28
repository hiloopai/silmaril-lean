module

public import Silmaril.Formats.Parquet.Reader.Recursive.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms
import Silmaril.Semantics.Relational.Table.Thms

namespace Silmaril.Proofs.Formats.Parquet.Reader.Recursive

open Silmaril.Formats
open Silmaril.Relational (AlignedColumns)
open Parquet.Reader.Recursive
open Arrow.RecursiveSchema.Stream.Events (Signature Value eraseBatch eraseRow projectTrace projectTrace_id)

private theorem map_const {α β : Type} (rows : List α) (value : β) :
    rows.map (fun _ => value) = List.replicate rows.length value := by
  induction rows <;> simp_all [List.replicate_succ]

private theorem empty_batch {source : Signature} (batch : Arrow.Events.Batch source Value) :
    eraseBatch ((Selection.empty.columns source).projectColumns batch) =
      Selection.empty.batch (eraseBatch batch) := by
  let columns := (Selection.empty.columns source).projectColumns batch
  have erased : ∀ row : Silmaril.Relational.Scan.Row (Selection.empty.columns source).schema Value,
      eraseRow row = [] := fun _ => rfl
  change ⟨columns.rowCount, columns.toRows.map eraseRow⟩ = Selection.empty.batch (eraseBatch batch)
  have allRows : columns.toRows.map eraseRow = columns.toRows.map (fun _ => []) :=
    List.map_congr_left (fun row _ => erased row)
  rw [allRows, map_const, AlignedColumns.length_toRows]
  rfl

public theorem selected_batches (selection : Selection) {source : Signature} {Failure : Type}
    (events : Trace source Failure) :
    (projectTrace (selection.columns source) events).batches.map eraseBatch =
      (events.batches.map eraseBatch).map selection.batch := by
  cases selection
  · rw [Selection.columns, projectTrace_id]
    simp only [List.map_map]
    rfl
  · simp only [projectTrace, List.map_map]
    exact List.map_congr_left (fun batch _ => empty_batch batch)

end Silmaril.Proofs.Formats.Parquet.Reader.Recursive
