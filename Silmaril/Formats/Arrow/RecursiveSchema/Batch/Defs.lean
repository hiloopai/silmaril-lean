module

public import Silmaril.Formats.Arrow.RecursiveSchema.Defs
public import Silmaril.Formats.Arrow.Body.Defs

/-! Checked preorder layout of one uncompressed RecordBatch against the
recursive V5 Schema profile. Buffer regions and List offsets are checked.
Validity bits and integer values remain uninterpreted. -/

namespace Silmaril.Formats.Arrow.RecursiveSchema.Batch

@[expose] public section

structure Limits where
  schema : RecursiveSchema.Limits := {}
  /-- Maximum sum of physical FieldNode lengths in one batch. -/
  slots : Nat := 8 * 1024 * 1024
  deriving Repr

inductive Error where
  | schema (cause : RecursiveSchema.Error)
  | envelope (cause : Arrow.Error)
  | metadata (cause : Arrow.Error)
  | body (cause : Arrow.Error)
  | expectedRecord
  | missingNode (node : Nat)
  | missingBuffer (buffer : Nat)
  | node (index : Nat) (cause : Arrow.Error)
  | buffer (index : Nat) (cause : Arrow.Error)
  | nodeLength (node expected actual : Nat)
  | nullCount (node length count : Nat)
  | slots (node : Nat)
  | depth (node : Nat)
  | arity (node : Nat) (kind : Wire.Kind) (count : Nat)
  | region (buffer : Nat)
  | validityExtent (buffer : Nat)
  | payloadExtent (buffer expected actual : Nat)
  | offsetWord (buffer index : Nat)
  | offsetStart (buffer value : Nat)
  | offsetOrder (buffer index previous current : Nat)
  | extraNodes (used available : Nat)
  | extraBuffers (used available : Nat)
  deriving DecidableEq, Repr

inductive FieldLayout where
  | field (node : FieldNode) (validity : Buffer) (payload : Option Buffer)
      (children : List FieldLayout)
  deriving BEq, Repr

structure Carrier where
  metadata : KBytes
  header : Wire.BatchHeader
  body : KBytes
  slotLimit : Nat

structure Cursor where
  nodeIndex : Nat := 0
  bufferIndex : Nat := 0
  previousEnd : Nat := 0
  slots : Nat := 0
  deriving Repr

def Cursor.afterNode (cursor : Cursor) (node : FieldNode) : Cursor :=
  { cursor with nodeIndex := cursor.nodeIndex + 1, slots := cursor.slots + node.length }

def Cursor.afterBuffer (cursor : Cursor) (buffer : Buffer) : Cursor :=
  { cursor with bufferIndex := cursor.bufferIndex + 1, previousEnd := buffer.offset + buffer.length }

structure NodeWire (carrier : Carrier) (cursor : Cursor) (length : Nat) (node : FieldNode) :
    Prop where
  original : Wire.batchNode carrier.metadata carrier.header cursor.nodeIndex = .ok node
  length_eq : node.length = length
  count_bound : node.nullCount ≤ node.length
  slots_bound : cursor.slots + node.length ≤ carrier.slotLimit

structure BufferWire (carrier : Carrier) (cursor : Cursor) (buffer : Buffer) : Prop where
  original : Wire.batchBuffer carrier.metadata carrier.header cursor.bufferIndex = .ok buffer
  region : buffer.Fits carrier.body.len cursor.previousEnd

def ValidityExtent (node : FieldNode) (buffer : Buffer) : Prop :=
  (buffer.length = 0 ∧ node.nullCount = 0) ∨
    (buffer.length > 0 ∧ node.length ≤ 8 * buffer.length)

instance (node : FieldNode) (buffer : Buffer) : Decidable (ValidityExtent node buffer) := by
  unfold ValidityExtent
  infer_instance

/-- Original nonnegative signed INT32 offsets from zero through the given
index. This includes offsets under null parent slots. -/
inductive OffsetPrefix (offsets : KBytes) : Nat → Nat → Prop where
  | zero : Body.offsetAt offsets 0 = some 0 → OffsetPrefix offsets 0 0
  | step {index previous current} :
      OffsetPrefix offsets index previous →
      Body.offsetAt offsets (index + 1) = some current →
      previous ≤ current →
      OffsetPrefix offsets (index + 1) current

def payloadBytes (kind : Wire.Kind) (length : Nat) : Nat :=
  match kind with
  | .struct => 0
  | .int32 => 4 * length
  | .int64 => 8 * length
  | .list => 4 * (length + 1)

inductive PayloadWire (carrier : Carrier) (cursor : Cursor) (node : FieldNode) :
    Wire.Kind → Option Buffer → Nat → Cursor → Prop where
  | struct : PayloadWire carrier cursor node .struct none node.length cursor
  | values {kind buffer} :
      (kind = .int32 ∨ kind = .int64) →
      BufferWire carrier cursor buffer →
      buffer.length = payloadBytes kind node.length →
      PayloadWire carrier cursor node kind (some buffer) node.length (cursor.afterBuffer buffer)
  | offsets {buffer childLength} :
      BufferWire carrier cursor buffer →
      payloadBytes .list node.length ≤ buffer.length →
      OffsetPrefix (Body.sliceBuffer carrier.body buffer) node.length childLength →
      PayloadWire carrier cursor node .list (some buffer) childLength (cursor.afterBuffer buffer)

mutual

/-- The node and its own buffers precede all child descriptors. The checked
List offsets determine the child length, and Struct children share its length. -/
inductive FieldWire (carrier : Carrier) :
    Nat → Nat → Field → Cursor → FieldLayout → Cursor → Prop where
  | field {depth length name nullable kind children start node validity payload childLength
      childStart childLayouts next} :
      validArity kind children.length = true →
      NodeWire carrier start length node →
      BufferWire carrier (start.afterNode node) validity →
      ValidityExtent node validity →
      PayloadWire carrier ((start.afterNode node).afterBuffer validity) node
        kind payload childLength childStart →
      FieldsWire carrier depth childLength children childStart childLayouts next →
      FieldWire carrier (depth + 1) length (.node name nullable kind children) start
        (.field node validity payload childLayouts) next

inductive FieldsWire (carrier : Carrier) :
    Nat → Nat → List Field → Cursor → List FieldLayout → Cursor → Prop where
  | nil {depth length cursor} : FieldsWire carrier depth length [] cursor [] cursor
  | cons {depth length field fields start layout layouts middle next} :
      FieldWire carrier depth length field start layout middle →
      FieldsWire carrier depth length fields middle layouts next →
      FieldsWire carrier depth length (field :: fields) start (layout :: layouts) next

end

structure FieldsResult (carrier : Carrier) (depth length : Nat) (fields : List Field)
    (start : Cursor) where
  layouts : List FieldLayout
  next : Cursor
  wire : FieldsWire carrier depth length fields start layouts next

structure Partition (carrier : Carrier) (depth : Nat) (schema : Schema) where
  fields : FieldsResult carrier depth carrier.header.rowCount schema.fields {}
  exact_nodes : fields.next.nodeIndex = carrier.header.nodeCount
  exact_buffers : fields.next.bufferIndex = carrier.header.bufferCount

end

private def witness {ε α : Type} (result : Except ε α) : Except ε {value // result = .ok value} :=
  match result with
  | .ok value => .ok ⟨value, rfl⟩
  | .error cause => .error cause

private theorem witness_ok {ε α : Type} {result : Except ε α} {value : α}
    (read : result = .ok value) : witness result = .ok ⟨value, read⟩ := by
  cases read
  rfl

private def readNode (carrier : Carrier) (cursor : Cursor) (length : Nat) :
    Except Error {node // NodeWire carrier cursor length node} := do
  let index := cursor.nodeIndex
  if index ≥ carrier.header.nodeCount then throw (.missingNode index)
  let ⟨node, wire⟩ ← witness (Wire.batchNode carrier.metadata carrier.header index)
    |>.mapError (.node index)
  if hLength : node.length = length then
    if hCount : node.nullCount ≤ node.length then
      if hSlots : cursor.slots + node.length ≤ carrier.slotLimit then
        return ⟨node, ⟨wire, hLength, hCount, hSlots⟩⟩
      else throw (.slots index)
    else throw (.nullCount index node.length node.nullCount)
  else throw (.nodeLength index length node.length)

private def readBuffer (carrier : Carrier) (cursor : Cursor) :
    Except Error {buffer // BufferWire carrier cursor buffer} := do
  let index := cursor.bufferIndex
  if index ≥ carrier.header.bufferCount then throw (.missingBuffer index)
  let ⟨buffer, wire⟩ ← witness (Wire.batchBuffer carrier.metadata carrier.header index)
    |>.mapError (.buffer index)
  if hRegion : buffer.Fits carrier.body.len cursor.previousEnd then
    return ⟨buffer, ⟨wire, hRegion⟩⟩
  else throw (.region index)

private def scanOffsets (offsets : KBytes) (buffer : Nat) :
    (remaining index previous : Nat) → OffsetPrefix offsets index previous →
    Except Error {last // OffsetPrefix offsets (remaining + index) last}
  | 0, _, previous, validated => .ok ⟨previous, (Nat.zero_add _).symm ▸ validated⟩
  | remaining + 1, index, previous, validated =>
    match word : Body.offsetAt offsets (index + 1) with
    | none => .error (.offsetWord buffer (index + 1))
    | some current =>
      if ordered : previous ≤ current then
        have step : OffsetPrefix offsets (index + 1) current := .step validated word ordered
        by
          simpa only [Nat.add_succ, Nat.succ_add] using
            scanOffsets offsets buffer remaining (index + 1) current step
      else .error (.offsetOrder buffer (index + 1) previous current)

private def readOffsets (offsets : KBytes) (buffer length : Nat) :
    Except Error {last // OffsetPrefix offsets length last} :=
  match word : Body.offsetAt offsets 0 with
  | none => .error (.offsetWord buffer 0)
  | some 0 => scanOffsets offsets buffer length 0 0 (.zero word)
  | some (value + 1) => .error (.offsetStart buffer (value + 1))

private structure PayloadResult (carrier : Carrier) (cursor : Cursor) (node : FieldNode)
    (kind : Wire.Kind) where
  buffer : Option Buffer
  length : Nat
  next : Cursor
  wire : PayloadWire carrier cursor node kind buffer length next

private def readPayload (carrier : Carrier) (cursor : Cursor) (node : FieldNode) :
    (kind : Wire.Kind) → Except Error (PayloadResult carrier cursor node kind)
  | .struct => .ok ⟨none, node.length, cursor, .struct⟩
  | .list => do
    let ⟨buffer, wire⟩ ← readBuffer carrier cursor
    if extent : payloadBytes .list node.length ≤ buffer.length then
      let ⟨childLength, offsets⟩ ← readOffsets (Body.sliceBuffer carrier.body buffer)
        cursor.bufferIndex node.length
      return ⟨some buffer, childLength, cursor.afterBuffer buffer, .offsets wire extent offsets⟩
    else throw (.payloadExtent cursor.bufferIndex (payloadBytes .list node.length) buffer.length)
  | .int32 => readValues .int32 (.inl rfl)
  | .int64 => readValues .int64 (.inr rfl)
where
  readValues (kind : Wire.Kind) (signed : kind = .int32 ∨ kind = .int64) :
      Except Error (PayloadResult carrier cursor node kind) := do
    let ⟨buffer, wire⟩ ← readBuffer carrier cursor
    if extent : buffer.length = payloadBytes kind node.length then
      return ⟨some buffer, node.length, cursor.afterBuffer buffer, .values signed wire extent⟩
    else throw (.payloadExtent cursor.bufferIndex (payloadBytes kind node.length) buffer.length)

private structure FieldResult (carrier : Carrier) (depth length : Nat) (field : Field) (start : Cursor) where
  layout : FieldLayout
  next : Cursor
  wire : FieldWire carrier depth length field start layout next

private def readFields (carrier : Carrier) (depth length : Nat)
    (readField : (field : Field) → (start : Cursor) →
      Except Error (FieldResult carrier depth length field start)) :
    (fields : List Field) → (start : Cursor) → Except Error (FieldsResult carrier depth length fields start)
  | [], start => .ok ⟨[], start, .nil⟩
  | field :: fields, start => do
    let head ← readField field start
    let tail ← readFields carrier depth length readField fields head.next
    return ⟨head.layout :: tail.layouts, tail.next, .cons head.wire tail.wire⟩

private def readField (carrier : Carrier) :
    (depth length : Nat) → (field : Field) → (start : Cursor) →
      Except Error (FieldResult carrier depth length field start)
  | 0, _, _, start => .error (.depth start.nodeIndex)
  | depth + 1, length, .node _ _ kind children, start => do
    if arity : validArity kind children.length = true then
      let ⟨node, nodeWire⟩ ← readNode carrier start length
      let afterNode := start.afterNode node
      let ⟨validity, validityWire⟩ ← readBuffer carrier afterNode
      if extent : ValidityExtent node validity then
        let payload ← readPayload carrier (afterNode.afterBuffer validity) node kind
        let children ← readFields carrier depth payload.length (readField carrier depth payload.length)
          children payload.next
        return ⟨.field node validity payload.buffer children.layouts, children.next,
          .field arity nodeWire validityWire extent payload.wire children.wire⟩
      else throw (.validityExtent afterNode.bufferIndex)
    else throw (.arity start.nodeIndex kind children.length)

/-- Partition the original node and buffer vectors exactly. Use a Carrier
with its header checked by `Wire.batchHeader` and its matching body.
`readFrame` establishes those conditions from a native envelope. -/
public def partition (carrier : Carrier) (depth : Nat) (schema : Schema) :
    Except Error (Partition carrier depth schema) := do
  let length := carrier.header.rowCount
  let fields ← readFields carrier depth length (readField carrier depth length) schema.fields {}
  if nodes : fields.next.nodeIndex = carrier.header.nodeCount then
    if buffers : fields.next.bufferIndex = carrier.header.bufferCount then
      return ⟨fields, nodes, buffers⟩
    else throw (.extraBuffers fields.next.bufferIndex carrier.header.bufferCount)
  else throw (.extraNodes fields.next.nodeIndex carrier.header.nodeCount)

public structure Frame (limits : Limits) (schema : Schema) (input : KBytes) (offset : Nat) where
  metadataSize : Nat
  header : Wire.BatchHeader
  body : KBytes
  layout : Partition ⟨input.slice (offset + 8) metadataSize, header, body, limits.slots⟩
    limits.schema.depth schema
  source_wf : input.wf = true
  envelope : Arrow.readEnvelope limits.schema.ipc input offset = .ok (.metadata metadataSize)
  metadata : Wire.batchHeader limits.schema.ipc (input.slice (offset + 8) metadataSize) = .ok header
  body_read : Arrow.readBody limits.schema.ipc input (offset + 8 + metadataSize) header.bodyLength = .ok body

@[expose] public def Frame.bodyStart {limits : Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (frame : Frame limits schema input offset) : Nat :=
  offset + 8 + frame.metadataSize

@[expose] public def Frame.next {limits : Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (frame : Frame limits schema input offset) : Nat :=
  frame.bodyStart + frame.header.bodyLength

@[expose] public def Frame.carrier {limits : Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (frame : Frame limits schema input offset) : Carrier :=
  ⟨input.slice (offset + 8) frame.metadataSize, frame.header, frame.body, limits.slots⟩

/-- The exact envelope and byte regions of the checked preorder partition. -/
public structure FrameWire {limits : Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (frame : Frame limits schema input offset) : Prop where
  prefix_wire : EnvelopeWire limits.schema.ipc input.toList offset (.metadata frame.metadataSize)
  metadata_bytes : frame.carrier.metadata.toList =
    (input.toList.drop (offset + 8)).take frame.metadataSize
  header_wire : Wire.batchHeader limits.schema.ipc frame.carrier.metadata = .ok frame.header
  body_bytes : frame.body.toList = (input.toList.drop frame.bodyStart).take frame.header.bodyLength
  body_bound : frame.body.len = frame.header.bodyLength ∧ frame.next ≤ input.len
  preorder : FieldsWire frame.carrier limits.schema.depth frame.header.rowCount schema.fields {}
    frame.layout.fields.layouts frame.layout.fields.next
  exact_nodes : frame.layout.fields.next.nodeIndex = frame.header.nodeCount
  exact_buffers : frame.layout.fields.next.bufferIndex = frame.header.bufferCount
  slots_bound : frame.layout.fields.next.slots ≤ limits.slots

/-- Validate a batch after its original metadata envelope was checked.
The retained carrier and exact envelope determine all subsequent slices. -/
public def readMetadataFrame (limits : Limits) (schema : Schema) (input : KBytes)
    (offset size : Nat) (wf : input.wf = true)
    (envelope : Arrow.readEnvelope limits.schema.ipc input offset = .ok (.metadata size)) :
    Except Error (Frame limits schema input offset) := do
  let metadata := input.slice (offset + 8) size
  let ⟨header, metadataWire⟩ ← witness (Wire.batchHeader limits.schema.ipc metadata)
    |>.mapError .metadata
  let ⟨body, bodyWire⟩ ← witness (Arrow.readBody limits.schema.ipc input
    (offset + 8 + size) header.bodyLength) |>.mapError .body
  let layout ← partition ⟨metadata, header, body, limits.slots⟩ limits.schema.depth schema
  return ⟨size, header, body, layout, wf, envelope, metadataWire, bodyWire⟩

/-- Validate one framed batch at the supplied cursor against a checked Schema.
The caller can use `Frame.next` to advance to the next envelope. -/
public def readFrame (limits : Limits) (schema : Schema) (input : KBytes) (offset : Nat) :
    Except Error (Frame limits schema input offset) := do
  if wf : input.wf = true then
    let ⟨.metadata size, envelope⟩ ← witness (Arrow.readEnvelope limits.schema.ipc input offset)
      |>.mapError .envelope | throw .expectedRecord
    readMetadataFrame limits schema input offset size wf envelope
  else throw (.envelope (.malformed .source))

/-- The framed entry point and the admitted-envelope entry point return
exactly the same layout or original typed failure. -/
public theorem readFrame_of_envelope {limits : Limits} {schema : Schema} {input : KBytes}
    {offset size : Nat} (wf : input.wf = true)
    (envelope : Arrow.readEnvelope limits.schema.ipc input offset = .ok (.metadata size)) :
    readFrame limits schema input offset = readMetadataFrame limits schema input offset size wf envelope := by
  unfold readFrame
  simp [wf, witness_ok envelope, bind, Except.bind, Except.mapError]

public structure First (limits : Limits) (input : KBytes) where
  schema : Schema
  offset : Nat
  schema_read : RecursiveSchema.readFrame limits.schema input = .ok (schema, offset)
  batch : Frame limits schema input offset

/-- Pair the first batch with the original checked schema in the same carrier. -/
public def readFirst (limits : Limits) (input : KBytes) : Except Error (First limits input) := do
  let ⟨(schema, offset), wire⟩ ← witness (RecursiveSchema.readFrame limits.schema input)
    |>.mapError .schema
  return ⟨schema, offset, wire, ← readFrame limits schema input offset⟩

end Silmaril.Formats.Arrow.RecursiveSchema.Batch
