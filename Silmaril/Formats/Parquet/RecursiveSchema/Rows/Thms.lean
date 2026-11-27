module

public import Silmaril.Formats.Parquet.RecursiveSchema.Rows.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Rows.Group

@[expose] public section

namespace Silmaril.Formats.Parquet.RecursiveSchema.Rows

open Arrow.RecursiveSchema.Batch.Rows (Observation)

theorem evidence_wire {group row : Nat} {columns : List Column} {input : List Evidence}
    (accepted : evidenceAt group row columns = .ok input) :
    List.Forall₂ (fun column (evidence : Evidence) =>
      evidence.column = column.location ∧ column.slots[row]? = some evidence.slot) columns input :=
  Proofs.Formats.Parquet.RecursiveSchema.Rows.evidence_wire accepted

theorem readColumn_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot} {group column : Nat}
    {result : Column} (accepted : readColumn limits schema group column = .ok result) :
    ColumnWire limits schema group column result :=
  Proofs.Formats.Parquet.RecursiveSchema.Rows.readColumn_wire accepted

/-- Successful rows fit the compiled Arrow schema. Their projection is
the exact classified evidence of every original signed chunk at that row. -/
theorem readGroup_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {schema : Compiled schemaLimits snapshot} {group : Nat}
    {output : Observation} (accepted : readGroup limits schema group = .ok output) :
    GroupWire limits schema group output :=
  Proofs.Formats.Parquet.RecursiveSchema.Rows.readGroup_wire accepted

theorem readAll_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {schema : Compiled schemaLimits snapshot} {output : List Observation}
    (accepted : readAll limits schema = .ok output) :
    List.Forall₂ (GroupWire limits schema) (List.range snapshot.groupCount) output :=
  Proofs.Formats.Parquet.RecursiveSchema.Rows.readAll_wire accepted

end Silmaril.Formats.Parquet.RecursiveSchema.Rows
