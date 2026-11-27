module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs

/-! Canonical uncompressed native V5 RecordBatch emission for the recursive
signed integer, Struct and List schema. A frame is written for an explicit
schema and observation, independently of stream assembly. -/

namespace Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer

@[expose] public section

inductive Error where
  | ipc (cause : Arrow.Error)
  | rowCount (expected actual : Nat)
  | rowWidth (slot expected actual : Nat)
  | structWidth (node slot expected actual : Nat)
  | kind (node slot : Nat) (expected : RecursiveSchema.Wire.Kind)
  | required (node slot : Nat)
  | arity (node : Nat) (kind : RecursiveSchema.Wire.Kind) (actual : Nat)
  | depth (node : Nat)
  | slots (node : Nat)
  | listOffset (node : Nat) (offset : Nat)
  | layout (cause : Batch.Error)
  | readback (cause : Rows.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

inductive Part where
  | validity (slots : List (Option Unit))
  | words (width : Nat) (values : List Nat)

def Part.size : Part → Nat
  | .validity slots => (slots.length + 7) / 8
  | .words width values => width * values.length

def Part.encode : Part → KBytes
  | .validity slots => Arrow.Writer.emitBitmap slots
  | .words width values => Arrow.Writer.emitWords width values

def padded (size : Nat) : Nat := size + Arrow.Writer.padding size

def partsExtent (parts : Array Part) : Nat :=
  (parts.toList.map fun part => padded part.size).sum

structure Plan where
  nodes : Array FieldNode := #[]
  parts : Array Part := #[]
  slots : Nat := 0
  bodyBytes : Nat := 0
  bodyExtent : bodyBytes = partsExtent parts := by rfl
  slotExtent : slots = (nodes.toList.map FieldNode.length).sum := by rfl

/-- Each window advances the offset by its size. A null slot contributes
zero, as does a present empty List. Validity distinguishes the two. -/
def listOffsets (sizes : List Nat) : List Nat :=
  sizes.scanl (· + ·) 0

def checkOffset (node offset : Nat) : Except Error Unit :=
  if offset ≥ 2^31 then .error (.listOffset node offset) else .ok ()

end

private def checkMetadata (ipc : Arrow.Limits) (nodes buffers : Nat) : Except Error Unit := do
  let size := MetadataWriter.Wire.batchSize nodes buffers
  if size ≥ 2^31 then throw (.ipc (.malformed .metadataLength))
  if size > ipc.metadataBytes then throw (.ipc (.limit .metadataBytes))

private def admitNode (limits : Batch.Limits) (plan : Plan) (kind : RecursiveSchema.Wire.Kind)
    (length : Nat) : Except Error Unit := do
  let node := plan.nodes.size
  if node ≥ limits.schema.ipc.fields then throw (.ipc (.limit .fields))
  if length ≥ 2^63 then throw (.ipc (.malformed .batchLayout))
  if plan.slots + length > limits.slots then throw (.slots node)
  let hasPayload := kind != .struct
  checkMetadata limits.schema.ipc (node + 1) (plan.parts.size + 1 + hasPayload.toNat)
  let bytes := plan.bodyBytes + padded ((length + 7) / 8) + padded (payloadBytes kind length)
  if bytes ≥ 2^63 then throw (.ipc (.malformed .bodyLength))
  if bytes > limits.schema.ipc.bodyBytes then throw (.ipc (.limit .bodyBytes))

/-- Outer absence is a physical slot hidden by a null Struct. It is
canonically valid, with zero integer words and empty List windows. Inner
absence is a visible logical null. -/
private abbrev Slot := Option Rows.Cell

private def Slot.valid : Slot → Option Unit
  | some none => none
  | _ => some ()

private def startNode (plan : Plan) (column : List Slot) : Plan :=
  let bits := column.map Slot.valid
  let length := column.length
  { nodes := plan.nodes.push ⟨length, bits.countP Option.isNone⟩
    parts := plan.parts.push (.validity bits)
    slots := plan.slots + length
    bodyBytes := plan.bodyBytes + padded ((length + 7) / 8)
    bodyExtent := by simp [partsExtent, Part.size, bits, length, plan.bodyExtent]
    slotExtent := by simp [length, ← plan.slotExtent] }

private def Plan.pushWords (plan : Plan) (width : Nat) (values : List Nat) : Plan :=
  { plan with
    parts := plan.parts.push (.words width values)
    bodyBytes := plan.bodyBytes + padded (width * values.length)
    bodyExtent := by simp [partsExtent, Part.size, plan.bodyExtent] }

private def readSlot {α : Type} (ordinal : Nat) (nullable : Bool) (kind : RecursiveSchema.Wire.Kind)
    (payload : Rows.Value → Option α) (index : Nat) (slot : Slot) : Except Error (Option α) :=
  match slot with
  | none => .ok none
  | some none => if nullable then .ok none else .error (.required ordinal index)
  | some (some value) =>
    match payload value with
    | some data => .ok (some data)
    | none => .error (.kind ordinal index kind)

private def readSlots {α : Type} (ordinal : Nat) (nullable : Bool) (kind : RecursiveSchema.Wire.Kind)
    (payload : Rows.Value → Option α) (slots : List Slot) : Except Error (List (Option α)) :=
  slots.mapIdxM (readSlot ordinal nullable kind payload)

private def rowArray (width : Nat) (badWidth : Nat → Nat → Error) (index : Nat)
    (row : Rows.Row) : Except Error (Array Rows.Cell) :=
  if row.length = width then .ok row.toArray else .error (badWidth index row.length)

/-- Before transposition, bound the workspace for all direct columns.
Each descendant reserves its own extent before it is expanded. -/
private def checkColumns (limits : Batch.Limits) (plan : Plan) (width length : Nat) :
    Except Error Unit :=
  if plan.slots + width * length ≤ limits.slots then .ok () else .error (.slots plan.nodes.size)

private abbrev Column := Unit → Except Error (List Slot)

private def planColumns (visit : Field → Column → Plan → Except Error Plan)
    (rows : List (Option (Array Rows.Cell))) :
    List Field → Nat → Plan → Except Error Plan
  | [], _, plan => .ok plan
  | field :: fields, index, plan => do
    let column : Column := fun _ => rows.mapIdxM fun slot row => do
      let some row := row | return none
      let some cell := row[index]? | throw (.rowWidth slot (index + 1) row.size)
      return some cell
    let next ← visit field column plan
    planColumns visit rows fields (index + 1) next

private def planField (limits : Batch.Limits) :
    Nat → Nat → Field → Column → Plan → Except Error Plan
  | 0, _, _, _, plan => .error (.depth plan.nodes.size)
  | depth + 1, length, .node _ nullable kind children, load, plan => do
    let ordinal := plan.nodes.size
    if !validArity kind children.length then throw (.arity ordinal kind children.length)
    admitNode limits plan kind length
    let column ← load ()
    let next := startNode plan column
    match kind with
    | .int32 =>
      let words ← readSlots ordinal nullable kind
        (fun | .int32 value => some value | _ => none) column
      return next.pushWords 4 (words.map fun word => (word.getD 0).toUInt32.toNat)
    | .int64 =>
      let words ← readSlots ordinal nullable kind
        (fun | .int64 value => some value | _ => none) column
      return next.pushWords 8 (words.map fun word => (word.getD 0).toUInt64.toNat)
    | .struct =>
      let width := children.length
      if width > 0 && depth == 0 then throw (.depth next.nodes.size)
      checkColumns limits next width length
      let rows ← readSlots ordinal nullable kind
        (fun | .struct fields => some fields | _ => none) column
      let indexed ← rows.mapIdxM fun index row => row.mapM
        (rowArray width (fun slot actual => .structWidth ordinal slot width actual) index)
      planColumns (planField limits depth length) indexed children 0 next
    | .list =>
      let [child] := children | throw (.arity ordinal kind children.length)
      if depth == 0 then throw (.depth next.nodes.size)
      let lists ← readSlots ordinal nullable kind
        (fun | .list elements => some elements | _ => none) column
      let windows := lists.map (·.getD [])
      let sizes := windows.map List.length
      let childLength := sizes.sum
      checkOffset ordinal childLength
      checkColumns limits next 1 childLength
      let offsets := listOffsets sizes
      let elements : Column := fun _ => .ok (windows.flatMap (List.map some))
      planField limits depth childLength child elements (next.pushWords 4 offsets)

/-- Check the row shape and resource limits while planning the original
preorder. Every padded extent is admitted before allocating byte buffers. -/
public def plan (limits : Batch.Limits) (schema : Schema) (input : Rows.Observation) :
    Except Error Plan := do
  let ipc := limits.schema.ipc
  if input.rowCount > ipc.rows then throw (.ipc (.limit .rows))
  if input.rowCount ≥ 2^63 then throw (.ipc (.malformed .batchLayout))
  if input.rows.length ≠ input.rowCount then throw (.rowCount input.rowCount input.rows.length)
  let width := schema.fields.length
  if width > ipc.fields then throw (.ipc (.limit .fields))
  checkMetadata ipc 0 0
  checkColumns limits {} width input.rowCount
  if width > 0 && limits.schema.depth == 0 then throw (.depth 0)
  let indexed ← input.rows.mapIdxM (rowArray width fun slot actual => .rowWidth slot width actual)
  planColumns (planField limits limits.schema.depth input.rowCount) (indexed.map some)
    schema.fields 0 {}

@[expose] public section

structure Encoded where
  metadata : RecordBatch
  body : KBytes

def encode (rowCount : Nat) (planned : Plan) : Encoded :=
  let (buffers, body) := Arrow.Writer.packBuffers 0 (planned.parts.toList.map Part.encode)
  ⟨⟨rowCount, planned.nodes.toList, buffers⟩, body⟩

structure EncodingWire (rowCount : Nat) (planned : Plan) (record : Encoded) : Prop where
  rows : record.metadata.rowCount = rowCount
  nodes : record.metadata.nodes = planned.nodes.toList
  bufferCount : record.metadata.buffers.length = planned.parts.size
  bodyExtent : record.body.len = planned.bodyBytes
  bodyAligned : record.body.len % 8 = 0
  regions : Arrow.Writer.PackedWire record.body.toList 0
    (planned.parts.toList.map Part.encode) record.metadata.buffers

def Encoded.message (record : Encoded) : Arrow.Message :=
  ⟨.recordBatch record.metadata, record.body.len⟩

/-- Build one modern RecordBatch envelope and its padded body. -/
def serialize (limits : Batch.Limits) (schema : Schema) (input : Rows.Observation) :
    Except Error KBytes := do
  let planned ← plan limits schema input
  let record := encode input.rowCount planned
  (StreamWriter.emitFrame limits.schema.ipc record.message record.body).mapError .ipc

def equalCell : Nat → Rows.Cell → Rows.Cell → Bool
  | _, none, none => true
  | depth + 1, some left, some right =>
    match left, right with
    | .int32 a, .int32 b => a == b
    | .int64 a, .int64 b => a == b
    | .struct a, .struct b | .list a, .list b => List.isEqv a b (equalCell depth)
    | _, _ => false
  | _, _, _ => false

def agrees (depth : Nat) (input output : Rows.Observation) : Bool :=
  input.rowCount == output.rowCount &&
    List.isEqv input.rows output.rows (fun left right => List.isEqv left right (equalCell depth))

/-- Certify the complete frame against the unchanged recursive layout and
logical row decoders. Hidden physical payloads have no logical comparison. -/
def emit (limits : Batch.Limits) (schema : Schema) (input : Rows.Observation) :
    Except Error KBytes := do
  let bytes ← serialize limits schema input
  let frame ← (readFrame limits schema bytes 0).mapError .layout
  let output ← (Rows.decode frame).mapError .readback
  if frame.next = bytes.len ∧ agrees limits.schema.depth input output = true then
    return bytes
  else throw .readbackMismatch

structure EmissionWire (limits : Batch.Limits) (schema : Schema) (input : Rows.Observation)
    (bytes : KBytes) : Prop where
  construction : ∃ planned, plan limits schema input = .ok planned ∧
    let record := encode input.rowCount planned
    StreamWriter.emitFrame limits.schema.ipc record.message record.body = .ok bytes
  readback : ∃ frame : Frame limits schema bytes 0,
    readFrame limits schema bytes 0 = .ok frame ∧ frame.next = bytes.len ∧
    Rows.decode frame = .ok input ∧ Rows.ObservationWire frame input

end

end Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer
