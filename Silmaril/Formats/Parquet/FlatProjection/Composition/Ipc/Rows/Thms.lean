module

public import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.Defs
import Silmaril.Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.Correctness

public section

namespace Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Rows

open Silmaril.Relational

/-- Successful EOS supplies one nullable slot per row in every declared field. -/
theorem readEvents_aligned {limits : Arrow.MixedFlat.Limits} {wire : KBytes} {observed : EventObservation}
    (read : readEvents limits wire = some observed) : Aligned observed :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.readEvents_aligned read

/-- The relational schema recovers every original descriptor by position. -/
theorem materialize_fields (observed : EventObservation) (aligned : Aligned observed) :
    List.ofFn (fun i => ((materialize observed aligned).schema.kind i).1) = observed.fields :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.materialize_fields observed aligned

/-- Every batch contributes its declared row count, including at width zero. -/
theorem materialize_rowCount (observed : EventObservation) (aligned : Aligned observed) :
    (materialize observed aligned).rowCount = (observed.batches.map Prod.fst).sum :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.materialize_rowCount observed aligned

/-- At each row and column position the transposition retains the original
nullable slot, including the full octet list of a present BinaryView cell. -/
theorem batchRows_cell (signature : Schema) (batch : BatchObservation)
    (aligned : BatchAligned signature.width batch) (row : Fin batch.1) (column : Fin signature.width) :
    ((batchColumns signature batch aligned).toRows.get (row.cast (List.length_ofFn).symm)) column =
      (batch.2[column.val]'(by simp [aligned.1])).get
        (row.cast (aligned.2 _ (List.getElem_mem _)).symm) :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.batchRows_cell signature batch aligned row column

/-- A typed Scan projection and its raw position list yield the same
dependent schema and ordered rows. The list may repeat positions or be empty. -/
theorem materialize_project (observed : EventObservation) (aligned : Aligned observed)
    (projection : Scan.Projection (schema observed.fields)) :
    ∃ output, ∃ outputAligned : Aligned output,
      projectEvents (positions projection) observed = some output ∧
        materialize output outputAligned =
          ⟨projection.schema, projection.project (materialize observed aligned).rows⟩ :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.materialize_project observed aligned projection

/-- Exact native exhaustion guarantees a materialized table. -/
theorem readRows_exact {limits : Arrow.MixedFlat.Limits} {wire : KBytes} {observed : EventObservation}
    (read : readEvents limits wire = some observed) :
    readRows limits wire = some (materialize observed (readEvents_aligned read)) :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.readRows_exact read

/-- Complete batch-sensitive equivalence implies equality of all ordered Scan rows. -/
theorem equivalent_rows {leftLimits rightLimits : Arrow.MixedFlat.Limits} {left right : KBytes}
    (same : Ipc.Equivalent leftLimits left rightLimits right) :
    Equivalent leftLimits left rightLimits right :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.equivalent_rows same

/-- A schema-only stream and a stream with one zero-row batch can carry
the same ordered Scan table and different complete batch observations. -/
theorem empty_batch_counterexample {leftLimits rightLimits : Arrow.MixedFlat.Limits} {left right : KBytes}
    {fields : List Arrow.MixedFlat.Field}
    (schemaOnly : readEvents leftLimits left = some ⟨fields, []⟩)
    (withEmpty : readEvents rightLimits right = some ⟨fields, [(0, fields.map fun _ => [])]⟩) :
    Equivalent leftLimits left rightLimits right ∧ ¬ Ipc.Equivalent leftLimits left rightLimits right :=
  Proofs.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.empty_batch_counterexample schemaOnly withEmpty

end Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Rows
