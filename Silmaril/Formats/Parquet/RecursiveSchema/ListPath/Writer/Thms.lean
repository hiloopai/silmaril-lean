module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Writer.File

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer

public section

/-- The column anchor and both footer sizes come from the same complete frame. -/
theorem GroupWire.footer_exact {limits : Limits} {checksum : Bool} {plan : Plan}
    {offset priorSlots : Nat} {input : Arrow.RecursiveSchema.Batch.Rows.Observation} {output : WrittenGroup}
    (wire : GroupWire limits checksum plan offset priorSlots input output) :
    ∃ column, (output.index plan).metadata.columns = [column] ∧
      (output.index plan).metadata.numRows = (input.rowCount : Int) ∧
      column.metadata.dataPageOffset = (offset : Int) ∧
      column.metadata.numValues = (output.slots : Int) ∧
      column.metadata.totalUncompressedSize = (output.page.wire.length : Int) ∧
      column.metadata.totalCompressedSize = (output.page.wire.length : Int) := by
  rw [← wire.atOffset, ← wire.rows]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The construction uses the original compiled declaration and emits one
contiguous canonical V1 frame per complete input group. -/
theorem serialize_construction {limits : Limits} {input : Input} {output : Output}
    (built : serialize limits input = .ok output) : Construction limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Writer.serialize_construction built

/-- The exact schema and complete ordered observations come from checking the
emitted file with the native reader and Events through EOS. -/
theorem certify_readback {limits : Limits} {input : Input} {output : Output}
    (accepted : certify limits input output = .ok ()) : Readback limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Writer.certify_readback accepted

theorem emit_wire {limits : Limits} {input : Input} {output : Output}
    (written : emit limits input = .ok output) : Construction limits input output ∧ Readback limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Writer.emit_wire written

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer
