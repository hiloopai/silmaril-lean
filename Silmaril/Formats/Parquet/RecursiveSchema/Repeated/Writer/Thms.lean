module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.File

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer

@[expose] public section

/-- The admitted page partition covers the input atoms and the chunk writer
certifies its exact wire bytes, counts and relative frames. -/
theorem writeColumn_wire {limits : Limits} {checksum : Bool} {group column rows : Nat}
    {start : Position} {leaf : Leaf} {atoms : List Rows.Atom} {cuts : Option (List Nat)}
    {placed : Placed}
    (written : writeColumn limits checksum group column rows start leaf atoms cuts = .ok placed) :
    ColumnWire limits checksum group column rows start leaf atoms cuts placed :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.column_wire written

theorem serialize_construction {limits : Limits} {input : Input} {output : Output}
    (written : serialize limits input = .ok output) : Construction limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.serialize_construction written

/-- The original native open and row-group readers agree with the input,
including exact schema, order, logical rows and explicit group counts. -/
theorem certify_readback {limits : Limits} {input : Input} {output : Output}
    (accepted : certify limits input output = .ok ()) : Readback limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.certify_readback accepted

theorem emit_wire {limits : Limits} {input : Input} {output : Output}
    (written : emit limits input = .ok output) :
    Construction limits input output ∧ Readback limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.emit_wire written

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer
