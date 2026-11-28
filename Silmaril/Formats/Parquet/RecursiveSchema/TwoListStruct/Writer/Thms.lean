module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.File

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer

public section

/-- The original footer records the two consecutive frame starts, both
slot counts and both header-inclusive sizes for each column. -/
theorem GroupWire.footer_exact {limits : Limits} {checksum : Bool} {plan : Plan} {offset priorSlots : Nat}
    {input : Arrow.RecursiveSchema.Batch.Rows.Observation} {output : WrittenGroup}
    (wire : GroupWire limits checksum plan offset priorSlots input output) :
    ∃ left right : Footer.ColumnChunk,
    (output.index plan).metadata.numRows = (input.rowCount : Int) ∧
    (output.index plan).metadata.columns = [left, right] ∧
    left.metadata.dataPageOffset = (offset : Int) ∧
    right.metadata.dataPageOffset = (output.middle offset : Int) ∧
    left.metadata.numValues = (output.left.slots : Int) ∧
    right.metadata.numValues = (output.right.slots : Int) ∧
    left.metadata.totalCompressedSize = (output.left.page.wire.length : Int) ∧
    left.metadata.totalUncompressedSize = (output.left.page.wire.length : Int) ∧
    right.metadata.totalCompressedSize = (output.right.page.wire.length : Int) ∧
    right.metadata.totalUncompressedSize = (output.right.page.wire.length : Int) :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.footer_exact wire

/-- The final envelope uses the checked declaration and two contiguous
canonical V1 frames per complete input group. -/
theorem serialize_construction {limits : Limits} {input : Input} {output : Output}
    (built : serialize limits input = .ok output) : Construction limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.serialize_construction built

/-- A separate native read certifies the exact declaration and ordered
groups, including the original byte and signed trace witnesses. -/
theorem certify_readback {limits : Limits} {input : Input} {output : Output}
    (accepted : certify limits input output = .ok ()) : Readback limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.certify_readback accepted

theorem emit_wire {limits : Limits} {input : Input} {output : Output}
    (written : emit limits input = .ok output) : Construction limits input output ∧ Readback limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.emit_wire written

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer
