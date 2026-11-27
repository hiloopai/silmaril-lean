module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Defs
public import Silmaril.Formats.Parquet.Plain.Defs
public import Mathlib.Data.List.Forall2

/-! The physical columns of one checked recursive RecordBatch.
Every node retains its own validity and its visibility through ancestors. -/

namespace Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics

@[expose] public section

inductive Error where
  | layout (cause : Batch.Error)
  | shape (node : Nat)
  | bitmap (node slot : Nat)
  | nullCount (node declared actual : Nat)
  | requiredNull (node slot : Nat)
  | words (node : Nat) (cause : Parquet.Plain.Error)
  | offset (node slot : Nat)
  deriving DecidableEq, Repr

structure Presence where
  /-- Whether all ancestors expose this physical slot. -/
  visible : Array Bool
  /-- This node's own stored validity, independent of ancestor visibility. -/
  valid : Array Bool
  deriving BEq, Repr

def Presence.present (presence : Presence) : Array Bool :=
  presence.visible.zipWith (· && ·) presence.valid

inductive Payload where
  | int32 (words : List Int32)
  | int64 (words : List Int64)
  | struct
  | list (offsets : Array Nat)
  deriving BEq, Repr

inductive Column where
  | node (presence : Presence) (payload : Payload) (children : List Column)
  deriving BEq, Repr

structure Observation where
  rowCount : Nat
  columns : List Column
  deriving BEq, Repr

def requiredNull (nullable : Bool) (presence : Presence) : Option Nat :=
  if nullable then none else
    (List.range presence.valid.size).find? fun i =>
      presence.visible[i]?.getD false && !presence.valid[i]?.getD false

def readPresence (body : KBytes) (index : Nat) (node : FieldNode) (buffer : Buffer)
    (nullable : Bool) (visible : Array Bool) : Except Error Presence := do
  if visible.size ≠ node.length then throw (.shape index)
  let bitmap := Body.sliceBuffer body buffer
  let bits ← (List.range node.length).mapM fun slot =>
    match Body.validAt bitmap slot with
    | some bit => .ok bit
    | none => .error (.bitmap index slot)
  let count := bits.countP (!·)
  if count ≠ node.nullCount then .error (.nullCount index node.nullCount count)
  else
    let presence : Presence := ⟨visible, bits.toArray⟩
    match requiredNull nullable presence with
    | some slot => .error (.requiredNull index slot)
    | none => .ok presence

def readPayload (body : KBytes) (index length : Nat) (kind : Wire.Kind)
    (buffer : Option Buffer) : Except Error Payload :=
  match kind, buffer with
  | .struct, none => .ok .struct
  | .int32, some buffer =>
    (Parquet.Plain.decodeInt32 length ⟨(Body.sliceBuffer body buffer).toByteArray⟩).map
      .int32 |>.mapError (.words index)
  | .int64, some buffer =>
    (Parquet.Plain.decodeInt64 length ⟨(Body.sliceBuffer body buffer).toByteArray⟩).map
      .int64 |>.mapError (.words index)
  | .list, some buffer => do
    let bytes := Body.sliceBuffer body buffer
    let offsets ← (List.range (length + 1)).mapM fun slot =>
      match Body.offsetAt bytes slot with
      | some value => .ok value
      | none => .error (.offset index slot)
    return .list offsets.toArray
  | _, _ => .error (.shape index)

/-- Copy the parent visibility bit to each member of the corresponding
List window. Checked offsets start at zero and delimit consecutive disjoint
windows, so the total expansion is exactly the physical child length. -/
def listVisibility (present : Array Bool) (offsets : Array Nat) : Array Bool :=
  ((List.range present.size).flatMap fun i =>
    List.replicate (offsets[i + 1]?.getD 0 - offsets[i]?.getD 0) (present[i]?.getD false)).toArray

def childVisibility (presence : Presence) (payload : Payload) : Array Bool :=
  match payload with
  | .list offsets => listVisibility presence.present offsets
  | .struct => presence.present
  | .int32 _ | .int64 _ => #[]

def decodeColumns (readColumn : Nat → Field → FieldLayout → Except Error (Column × Nat)) :
    Nat → List Field → List FieldLayout → Except Error (List Column × Nat)
  | index, [], [] => .ok ([], index)
  | index, field :: fields, layout :: layouts => do
    let (column, next) ← readColumn index field layout
    let (columns, next) ← decodeColumns readColumn next fields layouts
    return (column :: columns, next)
  | index, _, _ => .error (.shape index)

def decodeColumn (body : KBytes) :
    Nat → Array Bool → Nat → Field → FieldLayout → Except Error (Column × Nat)
  | 0, _, index, _, _ => .error (.shape index)
  | depth + 1, visible, index, .node _ nullable kind fields, .field node bitmap buffer layouts => do
    let presence ← readPresence body index node bitmap nullable visible
    let payload ← readPayload body index node.length kind buffer
    let (children, next) ← decodeColumns (decodeColumn body depth (childVisibility presence payload))
      (index + 1) fields layouts
    return (.node presence payload children, next)

/-- Decode the physical observation of one original checked frame.
The zero-width case retains the original row count. -/
def decode {limits : Batch.Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (frame : Frame limits schema input offset) : Except Error Observation := do
  let rows := frame.header.rowCount
  let visible := Array.replicate rows true
  let (columns, _) ← decodeColumns (decodeColumn frame.body limits.schema.depth visible)
    0 schema.fields frame.layout.fields.layouts
  return ⟨rows, columns⟩

/-- On a native IPC carrier, the checked layout runs before semantic decoding. -/
def readFirst (limits : Batch.Limits) (input : KBytes) :
    Except Error (First limits input × Observation) := do
  let first ← (Batch.readFirst limits input).mapError .layout
  return (first, ← decode first.batch)

structure PresenceWire (body : KBytes) (node : FieldNode) (buffer : Buffer) (nullable : Bool)
    (visible : Array Bool) (presence : Presence) : Prop where
  fromAncestors : presence.visible = visible
  visibilityLength : visible.size = node.length
  fromBitmap : List.Forall₂ (fun slot valid =>
    Body.validAt (Body.sliceBuffer body buffer) slot = some valid)
    (List.range node.length) presence.valid.toList
  nullCount : presence.valid.toList.countP (!·) = node.nullCount
  required : requiredNull nullable presence = none

/-- Signed words partition the complete original fixed-width region. -/
def SignedWords {α : Type} (width count : Nat) (value : List UInt8 → α)
    (bytes : KBytes) (observed : List α) : Prop :=
  ∃ words : List (List UInt8), bytes.toList = words.flatten ∧ words.length = count ∧
    (∀ word ∈ words, word.length = width) ∧ observed = words.map value

inductive PayloadWire (body : KBytes) (length : Nat) :
    Wire.Kind → Option Buffer → Payload → Prop where
  | struct : PayloadWire body length .struct none .struct
  | int32 {buffer words} :
      SignedWords 4 length (fun word => (Parquet.Plain.readUInt32Word word).toInt32)
        (Body.sliceBuffer body buffer) words →
      PayloadWire body length .int32 (some buffer) (.int32 words)
  | int64 {buffer words} :
      SignedWords 8 length (fun word => (Parquet.Plain.readUInt64Word word).toInt64)
        (Body.sliceBuffer body buffer) words →
      PayloadWire body length .int64 (some buffer) (.int64 words)
  | list {buffer offsets} :
      List.Forall₂ (fun slot value =>
        Body.offsetAt (Body.sliceBuffer body buffer) slot = some value)
        (List.range (length + 1)) offsets.toList →
      PayloadWire body length .list (some buffer) (.list offsets)

mutual

inductive ColumnWire (body : KBytes) :
    Array Bool → Field → FieldLayout → Column → Prop where
  | node {visible name nullable kind fields node bitmap buffer layouts presence payload children} :
    PresenceWire body node bitmap nullable visible presence →
    PayloadWire body node.length kind buffer payload →
    ColumnsWire body (childVisibility presence payload) fields layouts children →
    ColumnWire body visible (.node name nullable kind fields)
      (.field node bitmap buffer layouts) (.node presence payload children)

inductive ColumnsWire (body : KBytes) :
    Array Bool → List Field → List FieldLayout → List Column → Prop where
  | nil {visible} : ColumnsWire body visible [] [] []
  | cons {visible field fields layout layouts column columns} :
    ColumnWire body visible field layout column →
    ColumnsWire body visible fields layouts columns →
    ColumnsWire body visible (field :: fields) (layout :: layouts) (column :: columns)

end

/-- A descriptor anywhere in the ordered checked layout. -/
def buffers (layout : FieldLayout) : List Buffer :=
  match layout with
  | .field _ validity payload children =>
    validity :: payload.toList ++ children.flatMap buffers

structure ObservationWire {limits : Batch.Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (frame : Frame limits schema input offset) (observed : Observation) : Prop where
  frameWire : FrameWire frame
  rowCount : observed.rowCount = frame.header.rowCount
  columns : ColumnsWire frame.body (Array.replicate frame.header.rowCount true)
    schema.fields frame.layout.fields.layouts observed.columns
  absolute : ∀ buffer ∈ frame.layout.fields.layouts.flatMap buffers,
    (Body.sliceBuffer frame.body buffer).toList =
      (input.toList.drop (frame.bodyStart + buffer.offset)).take buffer.length

end

end Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics
