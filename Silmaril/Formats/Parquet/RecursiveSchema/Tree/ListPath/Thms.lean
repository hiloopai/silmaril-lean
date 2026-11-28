module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.ListPath.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.ListPath

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree

public section

/-- Projection preserves the signed leaf and all level thresholds used by
the existing scanner. The carrier keeps the original positional binding. -/
theorem LeafPath.projected_levels {path : LeafPath} {plan : ListPath.Plan}
    (projected : path.listPlan = some plan) :
    plan.shape.leaf = (path.site, path.kind) ∧ plan.shape.steps {} = path.steps ∧
      plan.shape.definitions = path.maxDefinition ∧ plan.shape.repetitions = path.maxRepetition ∧
      ListPath.Chunk.wrappers plan = path.repeated.map (·.emptyLevel) :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.projected_levels projected

theorem LeafBinding.read_wire {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled limits snapshot} {group column : Nat} {bound : LeafBinding compiled group column}
    {caps : ListPath.Chunk.Limits} {out : ListPath.Chunk.Observation} (read : bound.read caps = .ok out) :
    ListPath.Chunk.Wire caps bound.carrier out :=
  (ListPath.Chunk.readCarrier_wire read).1

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree
