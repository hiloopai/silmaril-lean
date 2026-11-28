module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Writer.File

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer

public section

/-- A native V1 page encodes the canonical levels and words of one complete group. -/
theorem writeGroup_wire {limits : Limits} {checksum : Bool} {plan : Plan}
    {ordinal offset already : Nat} {input : Arrow.RecursiveSchema.Batch.Rows.Observation} {output : WrittenGroup}
    (written : writeGroup limits checksum plan ordinal offset already input = .ok output) :
    GroupWire limits checksum plan offset already input output :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Writer.writeGroup_wire written

theorem serialize_construction {limits : Limits} {input : Input} {output : Output}
    (built : serialize limits input = .ok output) : Construction limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Writer.serialize_construction built

/-- The original checked readers recover the exact logical groups and EOS. -/
theorem certify_readback {limits : Limits} {input : Input} {output : Output}
    (accepted : certify limits input output = .ok ()) : Readback limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Writer.certify_readback accepted

theorem emit_wire {limits : Limits} {input : Input} {output : Output}
    (written : emit limits input = .ok output) : Construction limits input output ∧ Readback limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Writer.emit_wire written

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer
