module

public import Silmaril.Formats.Arrow.Metadata.Defs
public import Silmaril.Formats.Arrow.Writer.Defs

/-! FlatBuffers serialization for the flat Arrow V5 metadata profile.
The layouts place vtables before their tables and all uoffset targets after
their offset words. Metadata positions are relative to the root offset word. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MetadataWriter

namespace Wire

def words := Writer.emitWords 4
def longs := Writer.emitWords 8

/-- Two adjacent vtable halfwords in one little-endian word. -/
def halfwords (low high : Nat) : Nat := low + high * 65536

def pad (bytes : KBytes) : KBytes :=
  bytes ++ KBytes.zeros (Writer.padding bytes.len)

/-- A common 48-byte Message prefix. The root table starts at 24, and its
vtable and payload reference are at 4 and 32. -/
def messagePrefix (tag payload bodyLength : Nat) : KBytes :=
  words [24, halfwords 12 24, halfwords 4 6, halfwords 8 16, 0, 0,
    20, halfwords 4 tag, payload - 32, 0] ++ longs [bodyLength]

/-- Assemble a field with a 20-byte type fragment. The field table, type
table and name are at relative offsets 12, 36 and 48. -/
def fieldFragment (name : String) (nullable : Bool) (tag : Nat) (typeBytes : KBytes) : KBytes :=
  let nullableWord := if nullable then 1 else 0
  let nameBytes := Writer.emitWords 1 (name.toByteArray.data.toList.map UInt8.toNat)
  pad (words [halfwords 12 16, halfwords 4 8, halfwords 9 12,
      12, 32, nullableWord + tag * 256, 12] ++
      (typeBytes ++ (words [nameBytes.len] ++ (nameBytes ++ KBytes.zeros 1))))

/-- Encode the primitive Int or empty Utf8 table as specified in Schema.fbs. -/
def fieldBytes (field : Field) : KBytes :=
  let typeBytes := match field.type with
    | .int32 => words [halfwords 8 12, halfwords 4 8, 8, 32, 1]
    | .utf8 => words [halfwords 4 4, 0, 8, 0, 0]
  let tag := match field.type with
    | .int32 => 2
    | .utf8 => 5
  fieldFragment field.name field.nullable tag typeBytes

def fieldOffsets : Nat → Nat → List KBytes → List Nat
  | _, _, [] => []
  | slot, start, field :: rest =>
    (start + 12 - slot) :: fieldOffsets (slot + 4) (start + field.len) rest

/-- Assemble ordered field fragments under the relocatable Schema table at
byte eight. Place this payload at an eight-byte boundary. -/
def schemaPayloadOf (objects : List KBytes) : KBytes :=
  let vectorEnd := 20 + objects.length * 4
  let gap := Writer.padding vectorEnd
  let offsets := fieldOffsets 20 (vectorEnd + gap) objects
  words (halfwords 8 8 :: halfwords 0 4 :: 8 :: 4 :: objects.length :: offsets) ++
    (KBytes.zeros gap ++ objects.foldr (· ++ ·) KBytes.empty)

def schemaPayload (fields : List Field) : KBytes :=
  schemaPayloadOf (fields.map fieldBytes)

def schemaPayloadSize (fields : List Field) : Nat :=
  let vectorEnd := 20 + fields.length * 4
  vectorEnd + Writer.padding vectorEnd +
    (fields.map fun field =>
      let size := 53 + field.name.utf8ByteSize
      size + Writer.padding size).sum

def schemaBytes (fields : List Field) (bodyLength : Nat) : KBytes :=
  messagePrefix 1 56 bodyLength ++ schemaPayload fields

def batchSize (nodes buffers : Nat) : Nat :=
  104 + 16 * nodes + 16 * buffers

/-- The RecordBatch table starts at 64. The inline struct vectors have
four-byte length words and eight-byte-aligned 16-byte elements. -/
def batchBytes (batch : RecordBatch) (bodyLength : Nat) : KBytes :=
  messagePrefix 3 64 bodyLength ++
    (words [halfwords 10 24, halfwords 8 16, 20, 0, 16, 0] ++
      (longs [batch.rowCount] ++
        (words [12, 16 + 16 * batch.nodes.length, 0, batch.nodes.length] ++
          (longs (batch.nodes.flatMap fun node => [node.length, node.nullCount]) ++
            (words [0, batch.buffers.length] ++
              longs (batch.buffers.flatMap fun buffer => [buffer.offset, buffer.length]))))))

end Wire

open Wire

/-- Compute the metadata extent before encoding field names or building vectors. -/
def wireSize (message : Message) : Nat :=
  match message.header with
  | .schema fields => 48 + schemaPayloadSize fields
  | .recordBatch batch => batchSize batch.nodes.length batch.buffers.length

def checkDomain (limits : Limits) (message : Message) : Except Error Unit := do
  if message.bodyLength ≥ 2^63 then throw (.malformed .bodyLength)
  match message.header with
  | .schema fields =>
    if fields.length > limits.fields then throw (.limit .fields)
  | .recordBatch batch =>
    if batch.rowCount ≥ 2^63 then throw (.malformed .flatbuffer)
    if batch.rowCount > limits.rows then throw (.limit .rows)
    if batch.nodes.length > limits.fields || batch.buffers.length > 3 * limits.fields then
      throw (.limit .fields)
    if batch.nodes.any (fun node => node.length ≥ 2^63 || node.nullCount ≥ 2^63) ||
        batch.buffers.any (fun buffer => buffer.offset ≥ 2^63 || buffer.length ≥ 2^63) then
      throw (.malformed .flatbuffer)
def encode (message : Message) : KBytes :=
  match message.header with
  | .schema fields => schemaBytes fields message.bodyLength
  | .recordBatch batch => batchBytes batch message.bodyLength

/-- Serialize only the padded metadata region. Framing and batch layout are
stream-layer concerns. Signed wire ranges and configured limits are checked
before materializing bytes. -/
def serialize (limits : Limits) (message : Message) : Except Error KBytes :=
  match checkDomain limits message with
  | .error error => .error error
  | .ok () =>
    let size := wireSize message
    if size ≥ 2^31 then .error (.malformed .metadataLength)
    else if size > limits.metadataBytes then .error (.limit .metadataBytes)
    else .ok (encode message)

/-- Certify the metadata bytes using the existing reader, including exact
field order, descriptors, body length, and the explicit batch row count. -/
def emit (limits : Limits) (message : Message) : Except Error KBytes := do
  let bytes ← serialize limits message
  let decoded ← readMessage limits (bytes.slice 0 bytes.len)
  if decoded = message then return bytes
  else throw (.malformed .flatbuffer)

end Silmaril.Formats.Arrow.MetadataWriter
