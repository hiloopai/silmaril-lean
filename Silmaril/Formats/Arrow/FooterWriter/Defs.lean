module

public import Silmaril.Formats.Arrow.MetadataWriter.Defs

/-! FlatBuffers serialization for the supported Arrow V5 File.fbs footer. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.FooterWriter

open MetadataWriter.Wire

def wireSize (footer : FileFooter) : Nat :=
  40 + 24 * footer.blocks.length + schemaPayloadSize footer.fields

/-- The root table starts at 16. The block vector starts at 36 and its
24-byte structs start at byte 40. The schema payload follows the vector. -/
def encodeWithSchema (blocks : List FileBlock) (schema : KBytes) : KBytes :=
  let count := blocks.length
  words [16, halfwords 12 16, halfwords 4 8, halfwords 0 12, 12, 4, 24 + 24 * count, 8, 0, count] ++
    (longs (blocks.flatMap fun block => [block.offset, block.metadataLength, block.bodyLength]) ++
      schema)

def encode (footer : FileFooter) : KBytes :=
  encodeWithSchema footer.blocks (schemaPayload footer.fields)

def serialize (limits : Limits) (footer : FileFooter) : Except Error KBytes :=
  if footer.fields.length > limits.fields then .error (.limit .fields)
  else if footer.blocks.length > limits.batches then .error (.limit .batches)
  else if wireSize footer ≥ 2^31 then .error (.malformed .metadataLength)
  else if wireSize footer > limits.metadataBytes then .error (.limit .metadataBytes)
  else if footer.blocks.any
      (fun block => block.offset ≥ 2^63 || block.metadataLength ≥ 2^31 || block.bodyLength ≥ 2^63) then
    .error (.malformed .batchLayout)
  else .ok (encode footer)

/-- Check the footer AST against the existing decoder on the emitted
window. Extents in an enclosing file are checked by its index validator. -/
def emit (limits : Limits) (footer : FileFooter) : Except Error KBytes := do
  let bytes ← serialize limits footer
  let decoded ← readFileFooter limits (bytes.slice 0 bytes.len)
  if decoded = footer then return bytes
  else throw (.malformed .flatbuffer)

end Silmaril.Formats.Arrow.FooterWriter
