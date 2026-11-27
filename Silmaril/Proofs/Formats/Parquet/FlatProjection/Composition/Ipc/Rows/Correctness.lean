module

public import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.Defs
import Silmaril.Semantics.Relational.Scan.Thms
import Silmaril.Semantics.Relational.Table.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Rows

open Silmaril.Relational
open Silmaril.Formats Silmaril.Formats.Parquet.FlatProjection.Composition
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Rows

theorem readEvents_aligned {limits : Arrow.MixedFlat.Limits} {wire : KBytes} {observed : EventObservation}
    (read : readEvents limits wire = some observed) : Aligned observed := by
  unfold readEvents at read
  cases native : Arrow.MixedFlat.Stream.Events.readAll limits wire with
  | error error => simp [complete, native] at read
  | ok events =>
    obtain ⟨signature, trace⟩ := events
    cases termination : trace.termination <;> simp [complete, native, termination] at read
    subst observed
    intro batch hb
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp hb
    refine ⟨by simp [observeBatch], ?_⟩
    intro column hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    simpa [observeBatch] using original.length_eq i

theorem materialize_fields (observed : EventObservation) (aligned : Aligned observed) :
    List.ofFn (fun i => ((materialize observed aligned).schema.kind i).1) = observed.fields :=
  List.ofFn_getElem

theorem materialize_rowCount (observed : EventObservation) (aligned : Aligned observed) :
    (materialize observed aligned).rowCount = (observed.batches.map Prod.fst).sum := by
  have counts {signature : Schema} (batches : List BatchObservation)
      (each : ∀ batch ∈ batches, BatchAligned signature.width batch) :
      ((alignedBatches signature batches each).flatMap AlignedColumns.toRows).length =
        (batches.map Prod.fst).sum := by
    induction batches with
    | nil => rfl
    | cons head tail ih =>
      change ((batchColumns signature head _).toRows ++
        (alignedBatches signature tail _).flatMap AlignedColumns.toRows).length = _
      rw [List.length_append, AlignedColumns.length_toRows, ih]
      rfl
  exact counts (signature := schema observed.fields) observed.batches aligned

private theorem observeColumns_aligned {signature : Schema} (columns : Columns signature) :
    BatchAligned signature.width (observeColumns columns) := by
  refine ⟨by simp [observeColumns], ?_⟩
  intro column hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact columns.length_eq i

private theorem unpack_batch {signature : Schema} (columns : Columns signature)
    (aligned : BatchAligned signature.width (observeColumns columns)) :
    batchColumns signature (observeColumns columns) aligned = columns := by
  refine AlignedColumns.ext ?_ ?_
  · rfl
  · funext i
    simp [batchColumns, observeColumns]

private theorem unpack_batches {signature : Schema} (batches : List (Columns signature))
    (aligned : ∀ b ∈ batches.map observeColumns, BatchAligned signature.width b) :
    alignedBatches signature (batches.map observeColumns) aligned = batches := by
  induction batches with
  | nil => rfl
  | cons head tail ih =>
    change batchColumns signature (observeColumns head) _ :: alignedBatches signature (tail.map observeColumns) _ =
      head :: tail
    rw [unpack_batch, ih]

private theorem materialize_packed {signature : Schema} {fields : List Arrow.MixedFlat.Field}
    (same : schema fields = signature) (batches : List (Columns signature))
    (aligned : Aligned ⟨fields, batches.map observeColumns⟩) :
    materialize ⟨fields, batches.map observeColumns⟩ aligned =
      ⟨signature, batches.flatMap AlignedColumns.toRows⟩ := by
  subst signature
  unfold materialize
  rw [unpack_batches batches aligned]

private theorem schema_ext {α : Type} {n m : Nat} {left : Fin n → α} {right : Fin m → α}
    (width : n = m) (kinds : ∀ i, left i = right (i.cast width)) :
    (⟨n, left⟩ : PositionalSchema α) = ⟨m, right⟩ := by
  subst m
  have same : left = right := funext kinds
  rw [same]

private theorem schema_ofFn (signature : Schema) :
    schema (List.ofFn fun i => (signature.kind i).1) = signature := by
  cases signature with
  | mk width kind =>
    unfold schema Arrow.MixedFlat.Events.schema
    refine schema_ext (by simp) ?_
    intro i
    apply Prod.ext
    · simp
      rfl
    · exact Subsingleton.elim _ _

theorem toTable_columns (signature : Schema) (batches : List (Columns signature)) :
    toTable ⟨List.ofFn (fun i => (signature.kind i).1), batches.map observeColumns⟩ =
      some (⟨signature, batches.flatMap AlignedColumns.toRows⟩ : Table) := by
  let fields := List.ofFn (fun i => (signature.kind i).1)
  have aligned : Aligned ⟨fields, batches.map observeColumns⟩ := by
    intro batch member
    obtain ⟨columns, _, rfl⟩ := List.mem_map.mp member
    simpa [fields] using observeColumns_aligned columns
  change toTable ⟨fields, batches.map observeColumns⟩ = _
  rw [toTable, dite_eq_left aligned]
  exact congrArg some (materialize_packed (schema_ofFn signature) batches aligned)

private theorem select_ofFn {α : Type} {n w : Nat} (values : List α) (length : values.length = w)
    (indices : Fin n → Fin w) :
    select (List.ofFn fun i => (indices i).val) values =
      some (List.ofFn fun i => values[(indices i).val]'(by simp [length])) := by
  induction n with
  | zero => simp [select]
  | succ n ih =>
    simp only [List.ofFn_succ, select, List.mapM_cons] at ih ⊢
    rw [List.getElem?_eq_getElem (by simp [length]), ih]
    rfl

private theorem project_batch {signature : Schema} (projection : Scan.Projection signature)
    (batch : BatchObservation) (aligned : BatchAligned signature.width batch) :
    projectEventBatch (positions projection) batch =
      some (observeColumns (projection.projectColumns (batchColumns signature batch aligned))) := by
  unfold projectEventBatch positions
  rw [select_ofFn _ aligned.1 projection.index]
  rfl

private theorem project_batches {signature : Schema} (projection : Scan.Projection signature)
    (batches : List BatchObservation) (aligned : ∀ b ∈ batches, BatchAligned signature.width b) :
    batches.mapM (projectEventBatch (positions projection)) =
      some ((alignedBatches signature batches aligned).map (observeColumns ∘ projection.projectColumns)) := by
  induction batches with
  | nil => rfl
  | cons head rest ih =>
    change (head :: rest).mapM (projectEventBatch (positions projection)) =
      some (observeColumns (projection.projectColumns (batchColumns signature head _)) ::
        (alignedBatches signature rest _).map (observeColumns ∘ projection.projectColumns))
    rw [List.mapM_cons, project_batch projection head (aligned head (by simp)), ih]
    rfl

theorem materialize_project (observed : EventObservation) (aligned : Aligned observed)
    (projection : Scan.Projection (schema observed.fields)) :
    ∃ output, ∃ outputAligned : Aligned output,
      projectEvents (positions projection) observed = some output ∧
        materialize output outputAligned =
          ⟨projection.schema, projection.project (materialize observed aligned).rows⟩ := by
  let fields := List.ofFn fun i => (projection.schema.kind i).1
  let original := alignedBatches (schema observed.fields) observed.batches aligned
  let projected := original.map projection.projectColumns
  let output : EventObservation := ⟨fields, projected.map observeColumns⟩
  have alignedOutput : Aligned output := by
    intro batch member
    obtain ⟨columns, _, rfl⟩ := List.mem_map.mp member
    simpa [output, fields] using observeColumns_aligned columns
  refine ⟨output, alignedOutput, ?_, ?_⟩
  · have fieldPick : select (positions projection) observed.fields = some fields :=
      select_ofFn _ rfl projection.index
    have batchPick := project_batches projection observed.batches aligned
    simp [projectEvents, fieldPick, batchPick, output, projected, original,
      List.map_map, Bind.bind, Option.bind, pure]
  · have sameSchema : schema fields = projection.schema := schema_ofFn _
    change materialize ⟨fields, projected.map observeColumns⟩ alignedOutput = _
    rw [materialize_packed sameSchema]
    change Scan.Observation.mk projection.schema
      ((original.map projection.projectColumns).flatMap AlignedColumns.toRows) =
      ⟨projection.schema, projection.project (original.flatMap AlignedColumns.toRows)⟩
    congr 1
    simp only [Scan.Projection.project, List.flatMap_map, List.map_flatMap]
    congr 1
    funext batch
    exact projection.rowsEquiv_projectColumns batch

theorem batchRows_cell (signature : Schema) (batch : BatchObservation)
    (aligned : BatchAligned signature.width batch) (row : Fin batch.1) (column : Fin signature.width) :
    ((batchColumns signature batch aligned).toRows.get (row.cast (List.length_ofFn).symm)) column =
      (batch.2[column.val]'(by simp [aligned.1])).get
        (row.cast (aligned.2 _ (List.getElem_mem _)).symm) := by
  simp [AlignedColumns.toRows, batchColumns]
  rfl

theorem readRows_exact {limits : Arrow.MixedFlat.Limits} {wire : KBytes} {observed : EventObservation}
    (read : readEvents limits wire = some observed) :
    readRows limits wire = some (materialize observed (readEvents_aligned read)) := by
  simp [readRows, read, toTable, readEvents_aligned read]

theorem equivalent_rows {leftLimits rightLimits : Arrow.MixedFlat.Limits} {left right : KBytes}
    (same : Ipc.Equivalent leftLimits left rightLimits right) :
    Rows.Equivalent leftLimits left rightLimits right := by
  obtain ⟨observation, readLeft, readRight⟩ := same
  exact ⟨materialize observation (readEvents_aligned readLeft), readRows_exact readLeft,
    readRows_exact readRight⟩

theorem empty_batch_counterexample {leftLimits rightLimits : Arrow.MixedFlat.Limits} {left right : KBytes}
    {fields : List Arrow.MixedFlat.Field}
    (schemaOnly : readEvents leftLimits left = some ⟨fields, []⟩)
    (withEmpty : readEvents rightLimits right = some ⟨fields, [(0, fields.map fun _ => [])]⟩) :
    Rows.Equivalent leftLimits left rightLimits right ∧ ¬ Ipc.Equivalent leftLimits left rightLimits right := by
  refine ⟨⟨⟨schema fields, []⟩, ?_, ?_⟩, ?_⟩
  · rw [readRows_exact schemaOnly]
    rfl
  · rw [readRows_exact withEmpty]
    simp [materialize, alignedBatches, List.pmap, batchColumns, AlignedColumns.toRows]
  · rintro ⟨observation, leftRead, rightRead⟩
    rw [schemaOnly] at leftRead
    rw [withEmpty, ← Option.some.inj leftRead] at rightRead
    cases rightRead

end Silmaril.Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Rows
