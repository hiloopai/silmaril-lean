module

public import Silmaril.Formats.Arrow.Framing.Defs

/-! Checked FlatBuffers access for the Arrow V5 Message, Schema, Field and
RecordBatch IDLs. All offsets are relative to the padded metadata slice. -/

namespace Silmaril.Formats.Arrow

@[expose] public section

inductive FieldType where
  | int32 | utf8
  deriving DecidableEq, Repr

structure Field where
  name : String
  nullable : Bool
  type : FieldType
  deriving DecidableEq, Repr

structure FieldNode where
  length : Nat
  nullCount : Nat
  deriving DecidableEq, Repr

structure Buffer where
  offset : Nat
  length : Nat
  deriving DecidableEq, Repr

structure RecordBatch where
  rowCount : Nat
  nodes : List FieldNode
  buffers : List Buffer
  deriving DecidableEq, Repr

inductive MessageHeader where
  | schema (fields : List Field)
  | recordBatch (batch : RecordBatch)
  deriving DecidableEq, Repr

structure Message where
  header : MessageHeader
  bodyLength : Nat
  deriving DecidableEq, Repr


/-- Arrow V5 File.fbs Block. Metadata length includes the continuation prefix
and padding. The offset is absolute from the leading magic. -/
structure FileBlock where
  offset : Nat
  metadataLength : Nat
  bodyLength : Nat
  deriving DecidableEq, Repr

def FileBlock.endOffset (block : FileBlock) : Nat :=
  block.offset + block.metadataLength + block.bodyLength

/-- Supported V5 footer fields in their original index order. Version,
dictionaries and custom metadata are checked before constructing this AST. -/
structure FileFooter where
  fields : List Field
  blocks : List FileBlock
  deriving DecidableEq, Repr

end

private def check (condition : Bool) : Except Error Unit :=
  if condition then .ok () else .error (.malformed .flatbuffer)

private def require {α : Type} (result : Option α) : Except Error α :=
  match result with
  | some value => .ok value
  | none => .error (.malformed .flatbuffer)

private def uint (bytes : KBytes) (atByte width : Nat) : Except Error Nat :=
  require (bytes.readLE atByte width)

private def natural64 (bytes : KBytes) (atByte : Nat) : Except Error Nat := do
  let value ← uint bytes atByte 8
  check (value < 2^63)
  return value

/-- Unsigned forward references are relative to the offset word itself. -/
private def target (bytes : KBytes) (atByte : Nat) : Except Error Nat := do
  let delta ← uint bytes atByte 4
  check (4 ≤ delta && delta < 2^31)
  return atByte + delta

private structure Table where
  start : Nat
  stop : Nat
  vtable : Nat
  slots : Nat

private def table (bytes : KBytes) (start : Nat) : Except Error Table := do
  check (4 ≤ start && start % 4 == 0)
  let delta ← uint bytes start 4
  -- Deduplicated vtables can appear on either side of a table.
  let vtable := if delta < 2^31 then start - delta else start + (2^32 - delta)
  check (4 ≤ vtable && vtable % 2 == 0)
  let vsize ← uint bytes vtable 2
  let osize ← uint bytes (vtable + 2) 2
  check (4 ≤ vsize && vsize % 2 == 0 && vtable + vsize ≤ bytes.len)
  check (4 ≤ osize && start + osize ≤ bytes.len)
  check (vtable + vsize ≤ start || start + osize ≤ vtable)
  return ⟨start, start + osize, vtable, (vsize - 4) / 2⟩

private def tableShape (value : Table) (maxSlots : Nat) : Except Error Unit :=
  if value.slots ≤ maxSlots then .ok () else .error (.unsupported .unknownMetadataSlots)

private def slot (bytes : KBytes) (value : Table) (index width : Nat) :
    Except Error (Option Nat) := do
  if value.slots ≤ index then return none
  let delta ← uint bytes (value.vtable + 4 + index * 2) 2
  if delta == 0 then return none
  let pos := value.start + delta
  check (4 ≤ delta && pos % width == 0 && pos + width ≤ value.stop)
  return some pos

private def scalar (bytes : KBytes) (value : Table) (index width : Nat) : Except Error Nat := do
  match ← slot bytes value index width with
  | none => return 0
  | some pos => uint bytes pos width

private def reference (bytes : KBytes) (value : Table) (index : Nat) :
    Except Error (Option Nat) := do
  (← slot bytes value index 4).mapM (target bytes)

private def bool (bytes : KBytes) (value : Table) (index : Nat) : Except Error Bool := do
  let raw ← scalar bytes value index 1
  check (raw ≤ 1)
  return raw == 1

/-- Vector readers check the whole fixed-stride extent before enumerating any
elements. A nonempty element area can have stricter alignment than the
length word. -/
private def vector (bytes : KBytes) (value : Table) (index stride align : Nat) :
    Except Error (Nat × Nat) := do
  let some pos ← reference bytes value index | return (0, 0)
  let count ← uint bytes pos 4
  let first := pos + 4
  check (pos % 4 == 0 && (count == 0 || first % align == 0) &&
    first + count * stride ≤ bytes.len)
  return (first, count)

private def emptyVector (bytes : KBytes) (value : Table) (index stride align : Nat)
    (reason : Unsupported) : Except Error Unit := do
  let (_, count) ← vector bytes value index stride align
  if count ≠ 0 then throw (.unsupported reason)

private def noTable (bytes : KBytes) (value : Table) (index : Nat)
    (reason : Unsupported) : Except Error Unit := do
  if let some pos ← reference bytes value index then
    let _ ← table bytes pos
    throw (.unsupported reason)

private def string (bytes : KBytes) (value : Table) (index : Nat) : Except Error String := do
  let some pos ← reference bytes value index | return ""
  let count ← uint bytes pos 4
  let first := pos + 4
  check (pos % 4 == 0 && first + count < bytes.len)
  check ((← uint bytes (first + count) 1) == 0)
  let some name := String.fromUTF8? (bytes.slice first count).toByteArray
    | throw (.malformed .invalidUtf8)
  return name

private def field (bytes : KBytes) (pos : Nat) : Except Error Field := do
  let value ← table bytes pos
  tableShape value 7
  let name ← string bytes value 0
  let nullable ← bool bytes value 1
  let tag ← scalar bytes value 2 1
  check (tag != 0)
  let payload ← table bytes (← require (← reference bytes value 3))
  let type ← match tag with
    | 2 => do
      tableShape payload 2
      let width ← scalar bytes payload 0 4
      let signed ← bool bytes payload 1
      check (width == 8 || width == 16 || width == 32 || width == 64)
      if width != 32 || !signed then throw (.unsupported .fieldInteger)
      pure FieldType.int32
    | 5 => do
      tableShape payload 0
      pure FieldType.utf8
    | _ => throw (.unsupported (.fieldType tag))
  noTable bytes value 4 .dictionary
  emptyVector bytes value 5 4 4 .nested
  emptyVector bytes value 6 4 4 .customMetadata
  return ⟨name, nullable, type⟩

private def schema (limits : Limits) (bytes : KBytes) (value : Table) :
    Except Error (List Field) := do
  tableShape value 4
  let endian ← scalar bytes value 0 2
  if endian ≠ 0 then throw (.unsupported (.endianness endian))
  let (first, count) ← vector bytes value 1 4 4
  if count > limits.fields then throw (.limit .fields)
  emptyVector bytes value 2 4 4 .customMetadata
  emptyVector bytes value 3 8 8 .schemaFeatures
  (List.range count).mapM fun index => do
    field bytes (← target bytes (first + 4 * index))

private def batch (limits : Limits) (bytes : KBytes) (value : Table) :
    Except Error RecordBatch := do
  tableShape value 5
  let rowCount ← scalar bytes value 0 8
  check (rowCount < 2^63)
  if rowCount > limits.rows then throw (.limit .rows)
  let (nodeFirst, nodeCount) ← vector bytes value 1 16 8
  let (bufferFirst, bufferCount) ← vector bytes value 2 16 8
  if nodeCount > limits.fields || bufferCount > 3 * limits.fields then
    throw (.limit .fields)
  noTable bytes value 3 .compression
  emptyVector bytes value 4 8 8 .variadicBuffers
  let nodes ← (List.range nodeCount).mapM fun index => do
    let pos := nodeFirst + 16 * index
    pure (FieldNode.mk (← natural64 bytes pos) (← natural64 bytes (pos + 8)))
  let buffers ← (List.range bufferCount).mapM fun index => do
    let pos := bufferFirst + 16 * index
    pure (Buffer.mk (← natural64 bytes pos) (← natural64 bytes (pos + 8)))
  return ⟨rowCount, nodes, buffers⟩

/-- Decode only the metadata slice of a V5 Message. The stream reader checks
the envelope, message order and batch layout against the schema and body. -/
public def readMessage (limits : Limits) (bytes : KBytes) : Except Error Message := do
  if !bytes.wf then throw (.malformed .source)
  if bytes.len > limits.metadataBytes then throw (.limit .metadataBytes)
  let value ← table bytes (← target bytes 0)
  tableShape value 5
  let version ← scalar bytes value 0 2
  if version ≠ 4 then throw (.unsupported (.metadataVersion version))
  let tag ← scalar bytes value 1 1
  check (tag != 0)
  let payload ← table bytes (← require (← reference bytes value 2))
  let bodyLength ← scalar bytes value 3 8
  if bodyLength ≥ 2^63 then throw (.malformed .bodyLength)
  emptyVector bytes value 4 4 4 .customMetadata
  let header ← match tag with
    | 1 => MessageHeader.schema <$> schema limits bytes payload
    | 3 => MessageHeader.recordBatch <$> batch limits bytes payload
    | _ => throw (.unsupported (.messageKind tag))
  return ⟨header, bodyLength⟩

/-- Decode an Arrow V5 File.fbs footer from its checked file slice. -/
public def readFileFooter (limits : Limits) (bytes : KBytes) : Except Error FileFooter := do
  if !bytes.wf then throw (.malformed .source)
  if bytes.len > limits.metadataBytes then throw (.limit .metadataBytes)
  let value ← table bytes (← target bytes 0)
  tableShape value 5
  let version ← scalar bytes value 0 2
  if version ≠ 4 then throw (.unsupported (.metadataVersion version))
  emptyVector bytes value 2 24 8 .dictionary
  emptyVector bytes value 4 4 4 .customMetadata
  let schemaTable ← table bytes (← require (← reference bytes value 1))
  let fields ← schema limits bytes schemaTable
  let (first, count) ← vector bytes value 3 24 8
  if count > limits.batches then throw (.limit .batches)
  let blocks ← (List.range count).mapM fun index => do
    let pos := first + 24 * index
    let offset ← natural64 bytes pos
    let metadataLength ← uint bytes (pos + 8) 4
    check (metadataLength < 2^31)
    let bodyLength ← natural64 bytes (pos + 16)
    pure (FileBlock.mk offset metadataLength bodyLength)
  return ⟨fields, blocks⟩

end Silmaril.Formats.Arrow
