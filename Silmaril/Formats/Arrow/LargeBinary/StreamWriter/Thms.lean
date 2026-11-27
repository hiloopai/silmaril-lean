module

public import Silmaril.Formats.Arrow.LargeBinary.StreamWriter.Defs
import Silmaril.Proofs.Formats.Arrow.LargeBinary.StreamWriter.Correctness
import Silmaril.Formats.Arrow.Binary.StreamWriter.Thms

public section

namespace Silmaril.Formats.Arrow.LargeBinary.StreamWriter

theorem schema_extent (field : LargeBinary.Field) :
    (Binary.StreamWriter.Wire.schemaFor .i64 field.name field.nullable).len =
      Binary.StreamWriter.Wire.schemaSizeFor field.name :=
  Binary.StreamWriter.Wire.schemaFor_extent .i64 field.name field.nullable

/-- Successful emission gives exact ordered nullable octets and original
reader ranges through EOS. The writer relation records the canonical packed
buffers and per-message bounds. -/
theorem emit_readback {limits : Limits} {field : LargeBinary.Field}
    {batches : List LargeBinary.Column} {wire : KBytes}
    (written : emit limits field batches = .ok wire) :
    ∃ decoded, Stream.read limits .modern wire = .ok decoded ∧
      Agrees field batches decoded ∧ Stream.StreamWire limits .modern wire decoded ∧
      Binary.StreamWriter.SerializedWire .i64 limits field.name field.nullable batches wire :=
  Proofs.Formats.Arrow.LargeBinary.StreamWriter.emit_readback written

end Silmaril.Formats.Arrow.LargeBinary.StreamWriter
