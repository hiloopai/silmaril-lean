module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.Partition
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.Group

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows

open Arrow.RecursiveSchema.Batch.Rows (Row Observation)

@[expose] public section

/-- The slices exhaust the original addressed slots in order. Every slice
has exactly one row start followed only by continuations. -/
theorem partition_wire {slots : List Addressed} {rows : List (List Addressed)}
    (accepted : partition slots = .ok rows) : PartitionWire slots rows :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.partition_wire accepted

theorem readColumn_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot}
    {group column : Nat} {result : Column}
    (accepted : readColumn limits schema group column = .ok result) :
    ColumnWire limits schema group column result :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.readColumn_wire accepted

/-- Concatenating the checked rows of one physical column recovers the
original page-order levels, classifications and optional signed words. -/
theorem ColumnWire.original_atoms {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot}
    {group column : Nat} {result : Column} (wire : ColumnWire limits schema group column result) :
    ∃ (binding : Chunk.Binding schema group column) (observed : Chunk.Observation),
      Chunk.Wire limits binding observed ∧
      (result.rows.toList.flatMap (·.toList)).map Addressed.atom =
        observed.pages.flatMap (fun page =>
          (page.decoded.levels.zip page.decoded.words).map (fun (levels, word) => ⟨levels, word⟩)) :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.original_atoms wire

theorem readAt_wire {depth group row : Nat} {fields : List Field}
    {columns : List Column} {output : Row} (accepted : readAt depth group row fields columns = .ok output) :
    RowWire depth ⟨group, row, none⟩ fields columns output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.readAt_wire accepted

/-- The result has the original row count and fits the Arrow declaration.
The column partitions cover every source slot and projection recovers
the original repetition, definition, classification and word at each row. -/
theorem readGroup_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {schema : Compiled schemaLimits snapshot} {group : Nat} {output : Observation}
    (accepted : readGroup limits schema group = .ok output) : GroupWire limits schema group output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.readGroup_wire accepted

theorem readAll_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {schema : Compiled schemaLimits snapshot} {output : List Observation}
    (accepted : readAll limits schema = .ok output) :
    List.Forall₂ (GroupWire limits schema) (List.range snapshot.groupCount) output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.readAll_wire accepted

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows
