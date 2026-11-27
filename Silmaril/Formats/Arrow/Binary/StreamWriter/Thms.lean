module

public import Silmaril.Formats.Arrow.Binary.StreamWriter.Defs
import Silmaril.Proofs.Formats.Arrow.Binary.StreamWriter.Correctness
import Silmaril.Proofs.Formats.Arrow.Binary.StreamWriter.Bounds

public section

namespace Silmaril.Formats.Arrow.Binary.StreamWriter

theorem Wire.schemaProfile_extent (profile : Profile) (name : String) (nullable : Bool) :
    (schemaProfile profile name nullable).len = schemaSizeFor name :=
  Proofs.Formats.Arrow.Binary.StreamWriter.schemaProfile_extent profile name nullable

theorem serializeProfile_exact {profile : Profile} {limits : Limits}
    {name : String} {nullable : Bool} {batches : List Binary.Column} {wire : KBytes}
    (written : serializeProfile profile limits name nullable batches = .ok wire) :
    SerializedProfileWire profile limits name nullable batches wire :=
  Proofs.Formats.Arrow.Binary.StreamWriter.serializeProfile_exact written

theorem Wire.schemaFor_extent (width : Binary.Offsets.Width) (name : String) (nullable : Bool) :
    (schemaFor width name nullable).len = schemaSizeFor name :=
  Proofs.Formats.Arrow.Binary.StreamWriter.schemaFor_extent width name nullable

theorem serializeFor_exact {width : Binary.Offsets.Width} {limits : Limits}
    {name : String} {nullable : Bool} {batches : List Binary.Column} {wire : KBytes}
    (written : serializeFor width limits name nullable batches = .ok wire) :
    SerializedWire width limits name nullable batches wire :=
  Proofs.Formats.Arrow.Binary.StreamWriter.serializeFor_exact written

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
