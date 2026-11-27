module

public import Silmaril.Formats.Arrow.LargeUtf8.StreamWriter.Defs
import Silmaril.Proofs.Formats.Arrow.LargeUtf8.StreamWriter.Correctness
import Silmaril.Formats.Arrow.Binary.StreamWriter.Thms

public section

namespace Silmaril.Formats.Arrow.LargeUtf8.StreamWriter

theorem schema_extent (field : LargeUtf8.Field) :
    (Binary.StreamWriter.Wire.schemaProfile .largeUtf8 field.name field.nullable).len =
      Binary.StreamWriter.Wire.schemaSizeFor field.name :=
  Binary.StreamWriter.Wire.schemaProfile_extent .largeUtf8 field.name field.nullable

theorem encodeValue_octets (text : String) :
    (encodeValue text).toList = text.toByteArray.data.toList :=
  Proofs.Formats.Arrow.LargeUtf8.StreamWriter.encodeValue_octets text

theorem encodeColumn_dataSize (values : LargeUtf8.Column) :
    Binary.StreamWriter.dataSize (encodeColumn values) = Writer.utf8ByteCount values :=
  Proofs.Formats.Arrow.LargeUtf8.StreamWriter.encodeColumn_dataSize values

/-- Success gives exact field and ordered nullable strings, original reader
ranges through EOS, and canonical i64 offset buffers for the UTF-8 octets. -/
theorem emit_readback {limits : Limits} {field : LargeUtf8.Field}
    {batches : List LargeUtf8.Column} {wire : KBytes}
    (written : emit limits field batches = .ok wire) :
    ∃ decoded, Stream.read limits .modern wire = .ok decoded ∧
      Agrees field batches decoded ∧ Stream.StreamWire limits .modern wire decoded ∧
      Binary.StreamWriter.SerializedProfileWire .largeUtf8 limits field.name field.nullable
        (batches.map encodeColumn) wire :=
  Proofs.Formats.Arrow.LargeUtf8.StreamWriter.emit_readback written

end Silmaril.Formats.Arrow.LargeUtf8.StreamWriter
