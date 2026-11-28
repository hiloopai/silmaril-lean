module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Shared.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.Shared.Topology

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows

open RecursiveSchema (Location Site)
open Repeated (Compiled Leaf)
open Arrow.RecursiveSchema.Batch.Rows (Row Observation)

public section

/-- Both leaf paths pass through the same compiled LIST and Struct
steps. Only the independently optional child contributes another step. -/
theorem listStruct_steps {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {outer element : Site} {wrapper : Location} {left right : Leaf}
    (shape : schema.fields = [.list outer wrapper (.group element [.leaf left, .leaf right])]) :
    left.steps = sharedSteps outer wrapper element ++ childSteps left.site ∧
      right.steps = sharedSteps outer wrapper element ++ childSteps right.site :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.Shared.schema_steps schema shape

theorem listStruct_projection_topology {outer element : Site} {wrapper : Location} {left right : Leaf}
    {row : Row} {leftAtoms rightAtoms : List Atom} {depth : Nat}
    (leftSteps : left.steps = sharedSteps outer wrapper element ++ childSteps left.site)
    (rightSteps : right.steps = sharedSteps outer wrapper element ++ childSteps right.site)
    (projected : Projection.row depth [.list outer wrapper (.group element [.leaf left, .leaf right])] row =
      some [leftAtoms, rightAtoms]) :
    SharedTopology (sharedSteps outer wrapper element).length leftAtoms rightAtoms :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.Shared.projection_topology leftSteps rightSteps projected

/-- Successful reconstruction aligns the original addressed leaf slices
of each row at the common LIST and Struct definition ceiling. -/
theorem readGroup_listStruct_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {schema : Compiled schemaLimits snapshot} {group : Nat} {output : Observation}
    {outer element : Site} {wrapper : Location} {left right : Leaf}
    (shape : schema.fields = [.list outer wrapper (.group element [.leaf left, .leaf right])])
    (read : readGroup limits schema group = .ok output) :
    ListStructWire limits schema group (sharedSteps outer wrapper element).length output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.Shared.group_topology shape (readGroup_wire read)

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows
