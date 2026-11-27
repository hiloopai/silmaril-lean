module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics.Defs

/-! Positional logical rows of one checked recursive Arrow IPC batch.
Field names and declarations remain in the original schema. -/

namespace Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows

@[expose] public section

inductive Value where
  | int32 (word : Int32)
  | int64 (word : Int64)
  | struct (fields : List (Option Value))
  | list (elements : List (Option Value))
  deriving BEq, Repr

abbrev Cell := Option Value
abbrev Row := List Cell

structure Observation where
  rowCount : Nat
  rows : List Row
  deriving BEq, Repr

inductive SlotError where
  | depth (slot : Nat)
  | inaccessible (slot : Nat)
  | shape (slot : Nat)
  | offsets (slot : Nat)
  deriving DecidableEq, Repr

inductive Error where
  | source (cause : Semantics.Error)
  | row (index : Nat) (cause : SlotError)
  deriving DecidableEq, Repr

/-- Convert the physical signed columns once, so all subsequent slot
lookups are indexed even when a child belongs to a long List. -/
inductive IndexedPayload where
  | int32 (words : Array Int32)
  | int64 (words : Array Int64)
  | struct
  | list (offsets : Array Nat)

def IndexedPayload.ofPayload : Semantics.Payload → IndexedPayload
  | .int32 words => .int32 words.toArray
  | .int64 words => .int64 words.toArray
  | .struct => .struct
  | .list offsets => .list offsets

inductive IndexedColumn where
  | node (presence : Semantics.Presence) (payload : IndexedPayload) (children : List IndexedColumn)

def IndexedColumn.length : IndexedColumn → Nat
  | .node presence _ _ => presence.valid.size

def IndexedColumn.ofColumn (column : Semantics.Column) : IndexedColumn :=
  match column with
  | .node presence payload children =>
    .node presence (IndexedPayload.ofPayload payload) (children.map IndexedColumn.ofColumn)

def readCell : Nat → IndexedColumn → Nat → Except SlotError Cell
  | 0, _, slot => .error (.depth slot)
  | depth + 1, .node presence payload children, slot => do
    if presence.visible[slot]? != some true then throw (.inaccessible slot)
    match presence.valid[slot]? with
    | none => throw (.inaccessible slot)
    | some false => return none
    | some true =>
      match payload with
      | .int32 words =>
        let some word := words[slot]? | throw (.shape slot)
        return some (.int32 word)
      | .int64 words =>
        let some word := words[slot]? | throw (.shape slot)
        return some (.int64 word)
      | .struct =>
        let values ← children.mapM fun child => readCell depth child slot
        return some (.struct values)
      | .list offsets =>
        let [child] := children | throw (.shape slot)
        let some lo := offsets[slot]? | throw (.offsets slot)
        let some hi := offsets[slot + 1]? | throw (.offsets slot)
        if hi < lo || child.length < hi then throw (.offsets slot)
        let values ← (List.range' lo (hi - lo)).mapM (readCell depth child)
        return some (.list values)

/-- Materialize logical rows from physical columns. The physical schema
depth is the recursion budget. Each visible List window is traversed once. -/
def project (depth : Nat) (physical : Semantics.Observation) : Except Error Observation := do
  let columns := physical.columns.map IndexedColumn.ofColumn
  let rows ← (List.range physical.rowCount).mapM fun index =>
    (columns.mapM fun column => readCell depth column index).mapError (.row index)
  return ⟨physical.rowCount, rows⟩

def decode {limits : Batch.Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (frame : Frame limits schema input offset) : Except Error Observation := do
  let physical ← (Semantics.decode frame).mapError .source
  project limits.schema.depth physical

def readFirst (limits : Batch.Limits) (input : KBytes) :
    Except Error (First limits input × Observation) := do
  let (first, physical) ← (Semantics.readFirst limits input).mapError .source
  return (first, ← project limits.schema.depth physical)

def Reached (presence : Semantics.Presence) (slot : Nat) : Prop :=
  presence.visible[slot]? = some true

def Present (presence : Semantics.Presence) (slot : Nat) : Prop :=
  Reached presence slot ∧ presence.valid[slot]? = some true

mutual

/-- An independent logical slot relation over the checked physical columns.
A null node has no premises about any of its descendants. -/
inductive CellWire : Semantics.Column → Nat → Cell → Prop where
  | null {presence payload children slot} :
      Reached presence slot →
      presence.valid[slot]? = some false →
      CellWire (.node presence payload children) slot none
  | int32 {presence words children slot word} :
      Present presence slot →
      words[slot]? = some word →
      CellWire (.node presence (.int32 words) children) slot (some (.int32 word))
  | int64 {presence words children slot word} :
      Present presence slot →
      words[slot]? = some word →
      CellWire (.node presence (.int64 words) children) slot (some (.int64 word))
  | struct {presence children slot values} :
      Present presence slot →
      CellsWire (children.map fun child => (child, slot)) values →
      CellWire (.node presence .struct children) slot (some (.struct values))
  | list {presence offsets child slot lo hi values} :
      Present presence slot →
      offsets[slot]? = some lo →
      offsets[slot + 1]? = some hi →
      lo ≤ hi →
      CellsWire ((List.range' lo (hi - lo)).map fun index => (child, index)) values →
      CellWire (.node presence (.list offsets) [child]) slot (some (.list values))

inductive CellsWire : List (Semantics.Column × Nat) → Row → Prop where
  | nil : CellsWire [] []
  | cons {column slot positions cell cells} :
      CellWire column slot cell →
      CellsWire positions cells →
      CellsWire ((column, slot) :: positions) (cell :: cells)

end

mutual

inductive CellFits : Field → Cell → Prop where
  | null {name kind children} :
      CellFits (.node name true kind children) none
  | int32 {name nullable children word} :
      CellFits (.node name nullable .int32 children) (some (.int32 word))
  | int64 {name nullable children word} :
      CellFits (.node name nullable .int64 children) (some (.int64 word))
  | struct {name nullable children fields} :
      RowFits children fields →
      CellFits (.node name nullable .struct children) (some (.struct fields))
  | list {name nullable child elements} :
      RowFits (List.replicate elements.length child) elements →
      CellFits (.node name nullable .list [child]) (some (.list elements))

inductive RowFits : List Field → Row → Prop where
  | nil : RowFits [] []
  | cons {field fields cell cells} :
      CellFits field cell →
      RowFits fields cells →
      RowFits (field :: fields) (cell :: cells)

end

structure ProjectionWire (physical : Semantics.Observation) (logical : Observation) : Prop where
  rowCount : logical.rowCount = physical.rowCount
  positions : List.Forall₂ (fun slot row =>
    CellsWire (physical.columns.map fun column => (column, slot)) row)
    (List.range physical.rowCount) logical.rows

/-- The logical relation composes with the physical witness for the very
same schema, frame, descriptor vectors and absolute original bytes. -/
structure ObservationWire {limits : Batch.Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (frame : Frame limits schema input offset) (logical : Observation) : Prop where
  data : ∃ physical : Semantics.Observation,
    Semantics.ObservationWire frame physical ∧ ProjectionWire physical logical
  rowCount : logical.rowCount = frame.header.rowCount
  count : logical.rows.length = frame.header.rowCount
  typed : ∀ row ∈ logical.rows, RowFits schema.fields row

end

end Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows
