module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Defs
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Writer.Encoding
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Writer.Readback

@[expose] public section

namespace Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer

theorem bitmap_slot (slots : List (Option Unit)) (index : Nat) (bound : index < slots.length) :
    Body.validAt (Part.validity slots).encode index = some slots[index].isSome :=
  Arrow.Writer.emitBitmap_valid slots index bound

theorem word_at (width : Nat) (words : List Nat) (index : Nat) (bound : index < words.length) :
    (Part.words width words).encode.readLE (width * index) width =
      some (words[index] % 256^width) :=
  Arrow.Writer.readLE_emitWords width words index bound

/-- Each canonical List offset is the sum of the preceding window lengths. -/
theorem offset_at (sizes : List Nat) {index : Nat} (bound : index ≤ sizes.length) :
    (listOffsets sizes)[index]? = some (sizes.take index).sum :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Writer.offset_at sizes bound

/-- The shared packer realizes the exact planned byte windows and padded extent. -/
theorem encode_wire (rowCount : Nat) (planned : Plan) :
    EncodingWire rowCount planned (encode rowCount planned) :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Writer.encode_wire rowCount planned

theorem serialize_frame {limits : Batch.Limits} {schema : Schema} {input : Rows.Observation}
    {bytes : KBytes} (written : serialize limits schema input = .ok bytes) :
    ∃ planned, plan limits schema input = .ok planned ∧
      let record := encode input.rowCount planned
      StreamWriter.emitFrame limits.schema.ipc record.message record.body = .ok bytes :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Writer.serialize_frame written

/-- Success certifies a single whole native frame and the exact ordered
logical rows under the original schema, with the original byte witnesses. -/
theorem emit_wire {limits : Batch.Limits} {schema : Schema} {input : Rows.Observation}
    {bytes : KBytes} (written : emit limits schema input = .ok bytes) :
    EmissionWire limits schema input bytes :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Writer.emit_wire written

end Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer
