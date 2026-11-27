module

public import Silmaril.Formats.Arrow.Binary.StreamWriter.Defs
import Silmaril.Proofs.Formats.Arrow.Binary.StreamWriter.Correctness

public section

namespace Silmaril.Formats.Arrow.Binary.StreamWriter

theorem Wire.schema_extent (field : Binary.Field) : (schema field).len = schemaSize field :=
  Proofs.Formats.Arrow.Binary.StreamWriter.schema_extent field

/-- Success certifies exact field, nullable octets and ordered batch boundaries
through the existing stream reader, including its original ranges and EOS. -/
theorem emit_readback {limits : Limits} {field : Binary.Field}
    {batches : List Binary.Column} {wire : KBytes}
    (written : emit limits field batches = .ok wire) :
    ∃ decoded, Stream.read limits .modern wire = .ok decoded ∧
      Agrees field batches decoded ∧ Stream.StreamWire limits .modern wire decoded :=
  Proofs.Formats.Arrow.Binary.StreamWriter.emit_readback written

end Silmaril.Formats.Arrow.Binary.StreamWriter
