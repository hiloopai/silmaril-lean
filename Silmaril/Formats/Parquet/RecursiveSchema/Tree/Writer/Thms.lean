module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.Writer

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer

open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Repeated.Writer

public section

/-- The original footer anchor, slot count and both extents come from one
complete physical frame. -/
theorem ColumnWire.footer_exact {limits : Limits} {checksum : Bool} {leaf : LeafPlan}
    {offset : Nat} {atoms : List ListPath.Rows.Atom} {column : WrittenColumn}
    (wire : ColumnWire limits checksum leaf offset atoms column) :
    column.index.metadata.metadata.dataPageOffset = (offset : Int) ∧
      column.index.metadata.metadata.numValues = (atoms.length : Int) ∧
      column.index.metadata.metadata.totalUncompressedSize = (column.page.wire.length : Int) ∧
      column.index.metadata.metadata.totalCompressedSize = (column.page.wire.length : Int) := by
  rw [wire.index]
  simp [Schema.ColumnIndex.metadata, ListPath.Writer.frameSize_exact]

/-- Retrieve the original readback by the input group's positional index. -/
theorem GroupsReadback.group_at {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {compiled : Compiled schemaLimits snapshot}
    {ordinal : Nat} {inputs : List Observation} {groups : List WrittenGroup}
    (wire : GroupsReadback limits compiled ordinal inputs groups)
    {index : Nat} {input : Observation} (found : inputs[index]? = some input) :
    ∃ group, groups[index]? = some group ∧ GroupReadback limits compiled (ordinal + index) input group :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Writer.group_at wire found

/-- The certified read gives the exact input observation and signed traces
using the reopened original columns in their physical order. -/
theorem GroupReadback.original_group {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {compiled : Compiled schemaLimits snapshot}
    {ordinal : Nat} {input : Observation} {group : WrittenGroup}
    (wire : GroupReadback limits compiled ordinal input group) :
    ∃ result, Rows.readGroupChecked compiled limits.reader ordinal = .ok result ∧
      result.observation = input ∧
      (result.inputs.map fun column => column.original.atoms).toArray = group.traces ∧
      result.inputs.map Rows.CheckedColumn.ordinal = List.range compiled.leaves.size :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Writer.group_original wire

/-- Emitted bytes have both the canonical construction and an independent
native readback certificate for the exact input groups. -/
theorem emit_wire {limits : Limits} {input : Input} {out : Output}
    (written : emit limits input = .ok out) :
    ∃ groups, Construction limits input out groups ∧ Readback limits input out groups :=
  Proofs.Formats.Parquet.RecursiveSchema.Tree.Writer.emit_wire written

end

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.Writer
