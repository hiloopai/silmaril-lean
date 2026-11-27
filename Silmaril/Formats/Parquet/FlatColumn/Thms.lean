module

public import Silmaril.Formats.Parquet.FlatColumn.Defs
import Silmaril.Proofs.Formats.Parquet.FlatColumn.Wire

/-! Selected leaf and chunk ordinals, frame order and exact callback inputs. -/

public section

namespace Silmaril.Formats.Parquet.FlatColumn

theorem binding_leaf {snapshot : Snapshot.Checked} {selection : Selection}
    (binding : Binding snapshot selection) :
    snapshot.metadata.schema[binding.leafOrdinal]? = some binding.leaf ∧
    binding.leaf.name = selection.name ∧ binding.leaf.physicalType = some selection.physical ∧
    binding.leaf.repetition = some selection.layout.repetition :=
  ⟨binding.leafAt, binding.leafName, binding.leafPhysical, binding.leafRepetition⟩

/-- The checked callback retains the original frame checksum and payload. -/
theorem readColumnFor_checked_wire {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {policy : Policy} {decode : DecodePage α ε}
    {codec : CodecProfile} {index : Nat} {slots : List (Option α)}
    (read : readColumnFor codec binding limits policy decode index = .ok slots) :
    ∃ group, ColumnWireWith codec binding limits (CheckedCallbackWire codec limits decode binding.leaf)
      index group slots :=
  Proofs.Formats.Parquet.FlatColumn.readColumnFor_checked_wire read

/-- The selected codec profile shares the checked snapshot and ordered page walk. -/
theorem readColumnFor_wire {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {policy : Policy} {decode : DecodePage α ε}
    {codec : CodecProfile} {index : Nat} {slots : List (Option α)}
    (read : readColumnFor codec binding limits policy decode index = .ok slots) :
    ∃ group, ColumnWireFor codec binding limits decode index group slots :=
  Proofs.Formats.Parquet.FlatColumn.readColumnFor_wire read

/-- The original page parse and body-slice callback results occur in wire order,
and the flattened callback slots have the footer row count. -/
theorem readColumn_wire {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {policy : Policy} {decode : DecodePage α ε}
    {index : Nat} {slots : List (Option α)} (read : readColumn binding limits policy decode index = .ok slots) :
    ∃ group, ColumnWire binding limits decode index group slots :=
  readColumnFor_wire read

end Silmaril.Formats.Parquet.FlatColumn
