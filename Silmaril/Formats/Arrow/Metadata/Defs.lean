module

public import Silmaril.Formats.Arrow.Framing.Defs
public import Init.Data.Vector.OfFn

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

namespace SchemaReader

/-- Byte order recorded in the Schema, independently of body decoder support. -/
inductive Endianness where
  | little | big
  deriving DecidableEq, Repr

def Endianness.code : Endianness → Nat
  | .little => 0
  | .big => 1

inductive DateUnit where
  | day | millisecond
  deriving DecidableEq, Repr

def DateUnit.code : DateUnit → Nat
  | .day => 0
  | .millisecond => 1

/-- An omitted Date unit has the IDL default MILLISECOND. -/
def DateUnit.normalize (encoded : Option Nat) : Except Error DateUnit :=
  match encoded.getD 1 with
  | 0 => .ok .day
  | 1 => .ok .millisecond
  | _ => .error (.malformed .flatbuffer)

inductive TimestampUnit where
  | second | millisecond | microsecond | nanosecond
  deriving DecidableEq, Repr

def TimestampUnit.code : TimestampUnit → Nat
  | .second => 0
  | .millisecond => 1
  | .microsecond => 2
  | .nanosecond => 3

/-- An omitted Timestamp unit has the IDL default SECOND. -/
def TimestampUnit.normalize (encoded : Option Nat) : Except Error TimestampUnit :=
  match encoded.getD 0 with
  | 0 => .ok .second
  | 1 => .ok .millisecond
  | 2 => .ok .microsecond
  | 3 => .ok .nanosecond
  | _ => .error (.malformed .flatbuffer)

/-- Reader-only type payloads. The existing writer and stream AST use
`Arrow.FieldType` independently. -/
inductive FieldType where
  | primitive (type : Arrow.FieldType)
  | date (unit : DateUnit)
  | timestamp (unit : TimestampUnit) (timezone : Option String)
  deriving DecidableEq, Repr

structure Field where
  name : String
  nullable : Bool
  type : FieldType
  deriving DecidableEq, Repr

structure Schema where
  endianness : Endianness
  fields : List Field
  deriving DecidableEq, Repr

end SchemaReader

namespace Binary

/-- A flat plain Binary field (Schema.fbs union tag 4). -/
structure Field where
  name : String
  nullable : Bool
  deriving DecidableEq, Repr

inductive SchemaError where
  | metadata (cause : Arrow.Error)
  | fieldCount (actual : Nat)
  deriving DecidableEq, Repr

end Binary

namespace LargeBinary

/-- A flat LargeBinary field (Schema.fbs union tag 19). -/
structure Field where
  name : String
  nullable : Bool
  deriving DecidableEq, Repr

end LargeBinary

namespace LargeUtf8

/-- A flat LargeUtf8 field (Schema.fbs union tag 20). -/
structure Field where
  name : String
  nullable : Bool
  deriving DecidableEq, Repr

end LargeUtf8

namespace ListInt32

/-- The admitted nested field is a nullable List with one nullable signed
Int32 child. Retain both names from the wire schema. -/
structure Field where
  name : String
  childName : String
  deriving DecidableEq, Repr

end ListInt32

namespace StructInt32

/-- Explicit second-child profile. The first child is always signed Int32. -/
inductive RightWidth where
  | int32
  | int64
  deriving DecidableEq, Repr

abbrev RightWidth.Value : RightWidth → Type
  | .int32 => Int32
  | .int64 => Int64

structure Child where
  name : String
  nullable : Bool
  deriving DecidableEq, Repr

/-- A nullable Struct with two signed Int32 children in declared order. -/
structure Field where
  name : String
  left : Child
  right : Child
  deriving DecidableEq, Repr

end StructInt32

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

namespace BinaryView

inductive MetadataError where
  | metadata (cause : Arrow.Error)
  | nodeCount (actual : Nat)
  | countCardinality (actual : Nat)
  | negativeCount
  | dataBufferLimit
  | descriptorCount (expected actual : Nat)
  deriving DecidableEq, Repr

/-- Metadata for one preselected view field. The declared variadic count
determines the length and order of the data descriptor vector. -/
structure BatchMetadata (source : KBytes) (maxDataBuffers : Nat) where
  rowCount : Nat
  bodyLength : Nat
  node : FieldNode
  validity : Buffer
  views : Buffer
  countOffset : Nat
  dataCount : Nat
  data : Vector Buffer dataCount
  countWord : source.readLE countOffset 8 = some dataCount
  signedCount : dataCount < 2^63
  countWithin : dataCount ≤ maxDataBuffers

namespace Schema

inductive Kind where
  | binary | utf8
  deriving DecidableEq, Repr

def Kind.tag : Kind → Nat
  | .binary => 23
  | .utf8 => 24

def Kind.ofTag : Nat → Except Arrow.Error Kind
  | 23 => .ok .binary
  | 24 => .ok .utf8
  | tag => .error (.unsupported (.fieldType tag))

structure Field where
  name : String
  nullable : Bool
  kind : Kind
  deriving DecidableEq, Repr

inductive MetadataError where
  | metadata (cause : Arrow.Error)
  | fieldCount (actual : Nat)
  deriving DecidableEq, Repr

end Schema

end BinaryView

namespace MixedFlat

inductive Kind where
  | primitive (type : Arrow.FieldType)
  | view (type : BinaryView.Schema.Kind)
  deriving DecidableEq, Repr

def Kind.isView : Kind → Bool
  | .primitive _ => false
  | .view _ => true

def Kind.baseBuffers : Kind → Nat
  | .primitive .int32 | .view _ => 2
  | .primitive .utf8 => 3

structure Field where
  name : String
  nullable : Bool
  kind : Kind
  deriving DecidableEq, Repr

structure Metadata where
  batch : RecordBatch
  bodyLength : Nat
  counts : List Nat
  deriving DecidableEq, Repr

inductive MetadataError where
  | metadata (cause : Arrow.Error)
  | nodeCount (expected actual : Nat)
  | countCardinality (expected actual : Nat)
  | negativeCount (entry : Nat)
  | dataBufferLimit (entry : Nat)
  | totalDataBufferLimit
  | descriptorCount (expected actual : Nat)
  deriving DecidableEq, Repr


namespace LargeUtf8

/-- Opt-in schema kinds. LargeUtf8 shares the three-descriptor layout of
plain Utf8 and retains its distinct type for value decoding. -/
inductive Kind where
  | existing (kind : MixedFlat.Kind)
  | largeUtf8
  deriving DecidableEq, Repr

structure Field where
  name : String
  nullable : Bool
  kind : Kind
  deriving DecidableEq, Repr

/-- Project only the field's layout for the shared metadata and body binder. -/
def Field.layout (field : Field) : MixedFlat.Field :=
  ⟨field.name, field.nullable, match field.kind with
    | .existing kind => kind
    | .largeUtf8 => .primitive .utf8⟩

end LargeUtf8

end MixedFlat

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

structure MixedFlat.FileFooter where
  fields : List MixedFlat.Field
  blocks : List FileBlock
  deriving DecidableEq, Repr

/-- Normalized footer Schema and ordered absolute block descriptors. -/
structure SchemaReader.FileFooter where
  schema : SchemaReader.Schema
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

private def stringAt (bytes : KBytes) (pos : Nat) : Except Error String := do
  let count ← uint bytes pos 4
  let first := pos + 4
  check (pos % 4 == 0 && first + count < bytes.len)
  check ((← uint bytes (first + count) 1) == 0)
  let some name := String.fromUTF8? (bytes.slice first count).toByteArray
    | throw (.malformed .invalidUtf8)
  return name

private def optionalString (bytes : KBytes) (value : Table) (index : Nat) :
    Except Error (Option String) := do
  (← reference bytes value index).mapM (stringAt bytes)

private def string (bytes : KBytes) (value : Table) (index : Nat) : Except Error String := do
  return (← optionalString bytes value index).getD ""

private def checkSignedInteger (bytes : KBytes) (payload : Table) (expected : Nat) : Except Error Unit := do
  tableShape payload 2
  let width ← scalar bytes payload 0 4
  let signed ← bool bytes payload 1
  check (width == 8 || width == 16 || width == 32 || width == 64)
  if width != expected || !signed then throw (.unsupported .fieldInteger)

private def primitiveFieldType (bytes : KBytes) (tag : Nat) (payload : Table) :
    Except Error FieldType := do
  match tag with
  | 2 => do
    checkSignedInteger bytes payload 32
    return .int32
  | 5 => do
    tableShape payload 0
    return .utf8
  | _ => throw (.unsupported (.fieldType tag))

private def fieldWith {α β : Type} (bytes : KBytes) (pos : Nat)
    (typeOf : Nat → Table → Except Error α) (make : String → Bool → α → β) :
    Except Error β := do
  let value ← table bytes pos
  tableShape value 7
  let name ← string bytes value 0
  let nullable ← bool bytes value 1
  let tag ← scalar bytes value 2 1
  check (tag != 0)
  let payload ← table bytes (← require (← reference bytes value 3))
  let type ← typeOf tag payload
  noTable bytes value 4 .dictionary
  emptyVector bytes value 5 4 4 .nested
  emptyVector bytes value 6 4 4 .customMetadata
  return make name nullable type

private def field (bytes : KBytes) (pos : Nat) : Except Error Field :=
  fieldWith bytes pos (primitiveFieldType bytes) Field.mk

private def schemaWith {α β : Type} (limits : Limits) (bytes : KBytes) (value : Table)
    (endianOf : Nat → Except Error α) (fieldAt : Nat → Except Error β) :
    Except Error (α × List β) := do
  tableShape value 4
  let endian ← endianOf (← scalar bytes value 0 2)
  let (first, count) ← vector bytes value 1 4 4
  if count > limits.fields then throw (.limit .fields)
  emptyVector bytes value 2 4 4 .customMetadata
  emptyVector bytes value 3 8 8 .schemaFeatures
  let fields ← (List.range count).mapM fun index => do
    fieldAt (← target bytes (first + 4 * index))
  return (endian, fields)

private def schema (limits : Limits) (bytes : KBytes) (value : Table) :
    Except Error (List Field) :=
  (schemaWith limits bytes value
    (fun endian => if endian = 0 then .ok () else .error (.unsupported (.endianness endian)))
    (field bytes)).map Prod.snd

private def readSchemaEndianness : Nat → Except Error SchemaReader.Endianness
  | 0 => .ok .little
  | 1 => .ok .big
  | value => .error (.unsupported (.endianness value))

private def readSchemaFieldType (bytes : KBytes) (tag : Nat) (payload : Table) :
    Except Error SchemaReader.FieldType := do
  if tag = 8 then
    tableShape payload 1
    let unit ← (← slot bytes payload 0 2).mapM (fun pos => uint bytes pos 2)
    return .date (← SchemaReader.DateUnit.normalize unit)
  else if tag = 10 then
    tableShape payload 2
    let unit ← (← slot bytes payload 0 2).mapM (fun pos => uint bytes pos 2)
    return .timestamp (← SchemaReader.TimestampUnit.normalize unit) (← optionalString bytes payload 1)
  else
    return .primitive (← primitiveFieldType bytes tag payload)

private structure BatchVectors where
  rowCount : Nat
  nodeFirst : Nat
  nodeCount : Nat
  bufferFirst : Nat
  bufferCount : Nat

private def batchVectors (limits : Limits) (bytes : KBytes) (value : Table) :
    Except Error BatchVectors := do
  tableShape value 5
  let rowCount ← scalar bytes value 0 8
  check (rowCount < 2^63)
  if rowCount > limits.rows then throw (.limit .rows)
  let (nodeFirst, nodeCount) ← vector bytes value 1 16 8
  let (bufferFirst, bufferCount) ← vector bytes value 2 16 8
  return ⟨rowCount, nodeFirst, nodeCount, bufferFirst, bufferCount⟩

private def readNodeAt (bytes : KBytes) (first index : Nat) : Except Error FieldNode := do
  let pos := first + 16 * index
  return ⟨← natural64 bytes pos, ← natural64 bytes (pos + 8)⟩

private def readBufferAt (bytes : KBytes) (first index : Nat) : Except Error Buffer := do
  let pos := first + 16 * index
  return ⟨← natural64 bytes pos, ← natural64 bytes (pos + 8)⟩

private def batch (limits : Limits) (bytes : KBytes) (value : Table) :
    Except Error RecordBatch := do
  let vectors ← batchVectors limits bytes value
  if vectors.nodeCount > limits.fields || vectors.bufferCount > 3 * limits.fields then
    throw (.limit .fields)
  noTable bytes value 3 .compression
  emptyVector bytes value 4 8 8 .variadicBuffers
  let nodes ← (List.range vectors.nodeCount).mapM (readNodeAt bytes vectors.nodeFirst)
  let buffers ← (List.range vectors.bufferCount).mapM (readBufferAt bytes vectors.bufferFirst)
  return ⟨vectors.rowCount, nodes, buffers⟩

private def messageParts (limits : Limits) (bytes : KBytes) :
    Except Error (Nat × Table × Nat) := do
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
  return (tag, payload, bodyLength)

/-- Check the common V5 Message table and recover the body length for a
Schema or RecordBatch frame. The typed payload has its own decoder. -/
public def frameBodyLength (limits : Limits) (bytes : KBytes) : Except Error Nat := do
  let (tag, _, bodyLength) ← messageParts limits bytes
  if tag = 1 then
    if bodyLength = 0 then return 0
    else throw (.malformed .bodyLength)
  else if tag = 3 then return bodyLength
  else throw (.unsupported (.messageKind tag))

private def viewFieldKind (tag : Nat) (payload : Table) :
    Except Error BinaryView.Schema.Kind := do
  let kind ← BinaryView.Schema.Kind.ofTag tag
  tableShape payload 0
  return kind

private def singleBinarySchema {Field : Type} (limits : Limits) (bytes : KBytes)
    (typeTag : Nat) (makeField : String → Bool → Field) : Except Binary.SchemaError Field := do
  let (tag, payload, bodyLength) ← (messageParts limits bytes).mapError .metadata
  if tag ≠ 1 then throw (.metadata (.unsupported (.messageKind tag)))
  if bodyLength ≠ 0 then throw (.metadata (.malformed .bodyLength))
  let (_, fields) ← (schemaWith limits bytes payload
    (fun endian => if endian = 0 then .ok () else .error (.unsupported (.endianness endian)))
    (fun pos => fieldWith bytes pos
      (fun kind payload => do
        if kind ≠ typeTag then throw (.unsupported (.fieldType kind))
        tableShape payload 0)
      (fun name nullable () => makeField name nullable))).mapError .metadata
  let [field] := fields | throw (.fieldCount fields.length)
  return field

/-- Admit one plain Binary field from bodyless little-endian V5 Schema metadata. -/
public def Binary.readSchema (limits : Limits) (bytes : KBytes) :
    Except Binary.SchemaError Binary.Field :=
  singleBinarySchema limits bytes 4 Binary.Field.mk

/-- Admit one LargeBinary field from bodyless little-endian V5 Schema metadata. -/
public def LargeBinary.readSchema (limits : Limits) (bytes : KBytes) :
    Except Binary.SchemaError LargeBinary.Field :=
  singleBinarySchema limits bytes 19 LargeBinary.Field.mk

/-- Admit one LargeUtf8 field from bodyless little-endian V5 Schema metadata. -/
public def LargeUtf8.readSchema (limits : Limits) (bytes : KBytes) :
    Except Binary.SchemaError LargeUtf8.Field :=
  singleBinarySchema limits bytes 20 LargeUtf8.Field.mk

/-- Read the bodyless little-endian V5 Schema of a standalone one-field
view batch. Its kind is independent of legacy and other Schema readers. -/
public def BinaryView.Schema.readMessage (limits : Limits) (bytes : KBytes) :
    Except BinaryView.Schema.MetadataError BinaryView.Schema.Field := do
  let (tag, payload, bodyLength) ← (messageParts limits bytes).mapError .metadata
  if tag ≠ 1 then throw (.metadata (.unsupported (.messageKind tag)))
  if bodyLength ≠ 0 then throw (.metadata (.malformed .bodyLength))
  let (_, fields) ← (schemaWith limits bytes payload
    (fun endian => if endian = 0 then .ok () else .error (.unsupported (.endianness endian)))
    (fun pos => fieldWith bytes pos viewFieldKind BinaryView.Schema.Field.mk)).mapError .metadata
  let [field] := fields | throw (.fieldCount fields.length)
  return field

/-- Read V5 RecordBatch metadata for one preselected BinaryView or Utf8View
field. Validate the singleton count vector and descriptor cardinality
before reading its individual descriptors. -/
public def BinaryView.readBatchMetadata (limits : Limits) (maxDataBuffers : Nat) (bytes : KBytes) :
    Except BinaryView.MetadataError (BinaryView.BatchMetadata bytes maxDataBuffers) := do
  let (tag, payload, bodyLength) ← (messageParts limits bytes).mapError .metadata
  if tag ≠ 3 then throw (.metadata (.unsupported (.messageKind tag)))
  let vectors ← (batchVectors limits bytes payload).mapError .metadata
  if vectors.nodeCount > limits.fields then throw (.metadata (.limit .fields))
  if vectors.nodeCount ≠ 1 then throw (.nodeCount vectors.nodeCount)
  (noTable bytes payload 3 .compression).mapError .metadata
  let (first, entries) ← (vector bytes payload 4 8 8).mapError .metadata
  if entries ≠ 1 then throw (.countCardinality entries)
  match word : bytes.readLE first 8 with
  | none => throw (.metadata (.malformed .flatbuffer))
  | some count =>
    if signed : count < 2^63 then
      if within : count ≤ maxDataBuffers then
        if vectors.bufferCount ≠ 2 + count then
          throw (.descriptorCount (2 + count) vectors.bufferCount)
        let node ← (readNodeAt bytes vectors.nodeFirst 0).mapError .metadata
        let validity ← (readBufferAt bytes vectors.bufferFirst 0).mapError .metadata
        let views ← (readBufferAt bytes vectors.bufferFirst 1).mapError .metadata
        let data ← Vector.ofFnM
          (fun index : Fin count => (readBufferAt bytes vectors.bufferFirst (2 + index.val)).mapError .metadata)
        return ⟨vectors.rowCount, bodyLength, node, validity, views, first, count, data,
          word, signed, within⟩
      else throw .dataBufferLimit
    else throw .negativeCount

/-- A single List (type tag 12) whose sole child uses the existing
checked primitive field decoder. The legacy flat ASTs remain independent. -/
private def listInt32Field (parentNullable : Bool) (bytes : KBytes) (pos : Nat) : Except Error ListInt32.Field := do
  let value ← table bytes pos
  tableShape value 7
  let name ← string bytes value 0
  let nullable ← bool bytes value 1
  let tag ← scalar bytes value 2 1
  if tag ≠ 12 then throw (.unsupported (.fieldType tag))
  if nullable != parentNullable then throw (.unsupported .nested)
  let payload ← table bytes (← require (← reference bytes value 3))
  tableShape payload 0
  noTable bytes value 4 .dictionary
  let (start, count) ← vector bytes value 5 4 4
  if count ≠ 1 then throw (.unsupported .nested)
  let child ← field bytes (← target bytes start)
  if !child.nullable || child.type != .int32 then throw (.unsupported .nested)
  emptyVector bytes value 6 4 4 .customMetadata
  return ⟨name, child.name⟩

/-- Admit a bodyless, little-endian V5 List<Int32> schema message. -/
public def ListInt32.readSchemaFor (parentNullable : Bool) (limits : Limits) (bytes : KBytes) : Except Error ListInt32.Field := do
  let (tag, payload, bodyLength) ← messageParts limits bytes
  if tag ≠ 1 then throw (.unsupported (.messageKind tag))
  if bodyLength ≠ 0 then throw (.malformed .bodyLength)
  let (_, fields) ← schemaWith { limits with fields := min 1 limits.fields } bytes payload
    (fun endian => if endian = 0 then .ok () else .error (.unsupported (.endianness endian)))
    (listInt32Field parentNullable bytes)
  let [selected] := fields | throw (.unsupported .nested)
  return selected

@[expose] public def ListInt32.readSchema := ListInt32.readSchemaFor true

private def structRightChild (width : StructInt32.RightWidth) (bytes : KBytes) (pos : Nat) :
    Except Error (StructInt32.Child × Bool) :=
  match width with
  | .int32 => (field bytes pos).map (fun child => (⟨child.name, child.nullable⟩, child.type == .int32))
  | .int64 =>
    fieldWith bytes pos
      (fun tag payload => do
        if tag ≠ 2 then throw (.unsupported (.fieldType tag))
        checkSignedInteger bytes payload 64)
      (fun name nullable () => (⟨name, nullable⟩, true))

private def structInt32Field (width : StructInt32.RightWidth) (bytes : KBytes) (pos : Nat) :
    Except Error StructInt32.Field := do
  let value ← table bytes pos
  tableShape value 7
  let name ← string bytes value 0
  let nullable ← bool bytes value 1
  let tag ← scalar bytes value 2 1
  if tag ≠ 13 then throw (.unsupported (.fieldType tag))
  if !nullable then throw (.unsupported .nested)
  let payload ← table bytes (← require (← reference bytes value 3))
  tableShape payload 0
  noTable bytes value 4 .dictionary
  let (start, count) ← vector bytes value 5 4 4
  if count ≠ 2 then throw (.unsupported .nested)
  let left ← field bytes (← target bytes start)
  let (right, rightType) ← structRightChild width bytes (← target bytes (start + 4))
  if left.type != .int32 || !rightType then throw (.unsupported .nested)
  emptyVector bytes value 6 4 4 .customMetadata
  return ⟨name, ⟨left.name, left.nullable⟩, right⟩

/-- Admit the explicitly selected signed second-child width, with a signed
Int32 first child, in one bodyless little-endian V5 Struct Schema. -/
public def StructInt32.readSchemaFor (width : StructInt32.RightWidth) (limits : Limits) (bytes : KBytes) :
    Except Error StructInt32.Field := do
  let (tag, payload, bodyLength) ← messageParts limits bytes
  if tag ≠ 1 then throw (.unsupported (.messageKind tag))
  if bodyLength ≠ 0 then throw (.malformed .bodyLength)
  if limits.fields < 3 then throw (.limit .fields)
  let (_, fields) ← schemaWith { limits with fields := 1 } bytes payload
    (fun endian => if endian = 0 then .ok () else .error (.unsupported (.endianness endian)))
    (structInt32Field width bytes)
  let [selected] := fields | throw (.unsupported .nested)
  return selected

/-- The original profile requires two signed Int32 children. -/
@[expose] public def StructInt32.readSchema := StructInt32.readSchemaFor .int32

private def mixedFieldKind (bytes : KBytes) (tag : Nat) (payload : Table) :
    Except Error MixedFlat.Kind := do
  if tag == 23 || tag == 24 then
    return .view (← viewFieldKind tag payload)
  return .primitive (← primitiveFieldType bytes tag payload)

private def mixedSchemaWith {α : Type} (limits : Limits) (bytes : KBytes) (payload : Table)
    (fieldAt : Nat → Except Error α) : Except Error (List α) := do
  let (_, fields) ← schemaWith limits bytes payload
    (fun endian => if endian = 0 then .ok () else .error (.unsupported (.endianness endian)))
    fieldAt
  return fields

private def mixedSchema (limits : Limits) (bytes : KBytes) (payload : Table) :
    Except Error (List MixedFlat.Field) :=
  mixedSchemaWith limits bytes payload
    (fun pos => fieldWith bytes pos (mixedFieldKind bytes) MixedFlat.Field.mk)

private def readMixedSchema {α : Type} (limits : Limits) (bytes : KBytes)
    (decode : Table → Except Error (List α)) : Except Error (List α) := do
  let (tag, payload, bodyLength) ← messageParts limits bytes
  if tag ≠ 1 then throw (.unsupported (.messageKind tag))
  if bodyLength ≠ 0 then throw (.malformed .bodyLength)
  decode payload

/-- Admit the ordered fields of the bodyless little-endian mixed-flat Schema. -/
public def MixedFlat.readSchema (limits : Limits) (bytes : KBytes) :
    Except Error (List MixedFlat.Field) :=
  readMixedSchema limits bytes (mixedSchema limits bytes)

private def mixedLargeUtf8Kind (bytes : KBytes) (tag : Nat) (payload : Table) :
    Except Error MixedFlat.LargeUtf8.Kind := do
  if tag = 20 then
    tableShape payload 0
    return .largeUtf8
  return .existing (← mixedFieldKind bytes tag payload)

/-- Read the opt-in mixed schema with native LargeUtf8 (tag 20) in any
position, using the same V5 flat, little-endian checks. -/
public def MixedFlat.LargeUtf8.readSchema (limits : Limits) (bytes : KBytes) :
    Except Error (List MixedFlat.LargeUtf8.Field) :=
  readMixedSchema limits bytes fun payload =>
    mixedSchemaWith limits bytes payload
      (fun pos => fieldWith bytes pos (mixedLargeUtf8Kind bytes) MixedFlat.LargeUtf8.Field.mk)

/-- Bound count words and check the computed descriptor cardinality before
enumerating the nodes and descriptors. Count positions are view ordinals. -/
public def MixedFlat.readMetadata (limits : Limits) (perView totalData : Nat)
    (fields : List MixedFlat.Field) (bytes : KBytes) : Except MixedFlat.MetadataError MixedFlat.Metadata := do
  let (tag, payload, bodyLength) ← (messageParts limits bytes).mapError .metadata
  if tag ≠ 3 then throw (.metadata (.unsupported (.messageKind tag)))
  let vectors ← (batchVectors limits bytes payload).mapError .metadata
  if fields.length > limits.fields || vectors.nodeCount > limits.fields then
    throw (.metadata (.limit .fields))
  if vectors.nodeCount ≠ fields.length then throw (.nodeCount fields.length vectors.nodeCount)
  (noTable bytes payload 3 .compression).mapError .metadata
  let (first, entries) ← (vector bytes payload 4 8 8).mapError .metadata
  let expected := fields.countP (·.kind.isView)
  if entries ≠ expected then throw (.countCardinality expected entries)
  let counts ← (List.range entries).mapM fun entry => do
    let count ← (uint bytes (first + 8 * entry) 8).mapError MixedFlat.MetadataError.metadata
    if count ≥ 2^63 then throw (.negativeCount entry)
    if count > perView then throw (.dataBufferLimit entry)
    return count
  let dataCount := counts.sum
  if dataCount > totalData then throw .totalDataBufferLimit
  let expected := (fields.map (·.kind.baseBuffers)).sum + dataCount
  if vectors.bufferCount ≠ expected then throw (.descriptorCount expected vectors.bufferCount)
  let nodes ← ((List.range vectors.nodeCount).mapM (readNodeAt bytes vectors.nodeFirst)).mapError .metadata
  let buffers ← ((List.range vectors.bufferCount).mapM (readBufferAt bytes vectors.bufferFirst)).mapError .metadata
  return ⟨⟨vectors.rowCount, nodes, buffers⟩, bodyLength, counts⟩

private def normalizedSchema (limits : Limits) (bytes : KBytes) (payload : Table) :
    Except Error SchemaReader.Schema := do
  let (endian, fields) ← schemaWith limits bytes payload readSchemaEndianness
    (fun pos => fieldWith bytes pos (readSchemaFieldType bytes) SchemaReader.Field.mk)
  return ⟨endian, fields⟩

/-- Read a standalone V5 Schema message. The normalized type payloads and
schema byte order are available to readers without changing the existing IPC AST. -/
public def SchemaReader.readMessage (limits : Limits) (bytes : KBytes) :
    Except Error SchemaReader.Schema := do
  let (tag, payload, bodyLength) ← messageParts limits bytes
  if tag ≠ 1 then throw (.unsupported (.messageKind tag))
  if bodyLength ≠ 0 then throw (.malformed .bodyLength)
  normalizedSchema limits bytes payload

/-- Decode only the metadata slice of a V5 Message. The stream reader checks
the envelope, message order and batch layout against the schema and body. -/
public def readMessage (limits : Limits) (bytes : KBytes) : Except Error Message := do
  let (tag, payload, bodyLength) ← messageParts limits bytes
  let header ← match tag with
    | 1 => MessageHeader.schema <$> schema limits bytes payload
    | 3 => MessageHeader.recordBatch <$> batch limits bytes payload
    | _ => throw (.unsupported (.messageKind tag))
  return ⟨header, bodyLength⟩

private def fileFooterWith {α : Type} (limits : Limits) (bytes : KBytes)
    (readSchemaTable : Table → Except Error α) : Except Error (α × List FileBlock) := do
  if !bytes.wf then throw (.malformed .source)
  if bytes.len > limits.metadataBytes then throw (.limit .metadataBytes)
  let value ← table bytes (← target bytes 0)
  tableShape value 5
  let version ← scalar bytes value 0 2
  if version ≠ 4 then throw (.unsupported (.metadataVersion version))
  emptyVector bytes value 2 24 8 .dictionary
  emptyVector bytes value 4 4 4 .customMetadata
  let schemaTable ← table bytes (← require (← reference bytes value 1))
  let observed ← readSchemaTable schemaTable
  let (first, count) ← vector bytes value 3 24 8
  if count > limits.batches then throw (.limit .batches)
  let blocks ← (List.range count).mapM fun index => do
    let pos := first + 24 * index
    let offset ← natural64 bytes pos
    let metadataLength ← uint bytes (pos + 8) 4
    check (metadataLength < 2^31)
    let bodyLength ← natural64 bytes (pos + 16)
    pure (FileBlock.mk offset metadataLength bodyLength)
  return (observed, blocks)

/-- Decode an Arrow V5 File.fbs footer for the primitive profile. -/
public def readFileFooter (limits : Limits) (bytes : KBytes) : Except Error FileFooter := do
  let (fields, blocks) ← fileFooterWith limits bytes (schema limits bytes)
  return ⟨fields, blocks⟩

/-- Decode a footer for the four mixed-flat field kinds. -/
public def MixedFlat.readFileFooter (limits : Limits) (bytes : KBytes) : Except Error MixedFlat.FileFooter := do
  let (fields, blocks) ← fileFooterWith limits bytes (mixedSchema limits bytes)
  return ⟨fields, blocks⟩

/-- Decode the footer through the same normalized Schema parser as a Message. -/
public def SchemaReader.readFileFooter (limits : Limits) (bytes : KBytes) :
    Except Error SchemaReader.FileFooter := do
  let (schema, blocks) ← fileFooterWith limits bytes (normalizedSchema limits bytes)
  return ⟨schema, blocks⟩

end Silmaril.Formats.Arrow
