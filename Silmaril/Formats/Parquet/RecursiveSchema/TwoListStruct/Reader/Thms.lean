module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Read

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader

open Arrow.RecursiveSchema.Batch.Rows (Observation)

public section

/-- The first wrapper stops after the optional outer marker. The second
stops immediately below the shared required Struct. -/
theorem Plan.path_levels (plan : Plan) (side : Side) :
    (plan.path side).shape.repetitions = 2 ∧
      (plan.path side).shape.definitions = plan.sharedDefinition + (plan.child side).1.nullable.toNat ∧
      ListPath.Chunk.wrappers (plan.path side) =
        [plan.outer.site.nullable.toNat, plan.sharedDefinition - 1] :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.path_levels plan side

theorem readColumn_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {bound : GroupBinding snapshot group}
    {side : Side} {binding : ColumnBinding schema bound side} {limits : Limits}
    {out : ListPath.Chunk.Observation} (read : readColumn limits binding = .ok out) :
    ColumnWire limits binding out :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.column_wire read

/-- Successful reconstruction agrees on all shared ancestors and
projects each child back to its exact original signed slot trace. -/
theorem readGroup_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Limits} {out : Observation}
    (read : readGroup limits schema group = .ok out) : GroupWire limits schema group out :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.group_wire read

/-- A topology refusal has two independently checked original chunks
and reaches the first unmatched slot after their common prefix. -/
theorem readGroup_topology_failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Limits}
    {cause : Rows.TopologyError} (read : readGroup limits schema group = .error (.topology cause)) :
    GroupTopologyFailure limits schema group cause :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.group_topology_failure read

theorem readAll_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {limits : Limits} {out : List Observation}
    (read : readAll limits schema = .ok out) :
    List.Forall₂ (GroupWire limits schema) (List.range snapshot.groupCount) out :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.all_wire read

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader
