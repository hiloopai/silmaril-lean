module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Defs
public import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs

/-! Checked ordinal projections from flat PLAIN Parquet to native Arrow V5. -/

public section

namespace Silmaril.Formats.Parquet.FlatProjection

open Arrow.MixedFlat

structure Limits where
  column : Int32ByteArrayGroup.Limits := {}
  maxFileRows : Nat := 1024 * 1024
  maxFields : Nat := 64

inductive BindError where
  | missingLeaf
  | unsupportedPhysical (physical : Option Footer.PhysicalType)
  | unsupportedLayout (repetition : Option Footer.Repetition)
  | binding (cause : FlatColumn.BindError)
  | ordinalMismatch (actual : Nat)
  deriving DecidableEq, Repr

inductive SourceError where
  | fileByteLimit (maximum actual : Nat)
  | fileRowLimit (maximum actual : Nat)
  | fieldLimit (maximum actual : Nat)
  | snapshot (cause : Snapshot.Error Unit)
  | bind (position ordinal : Nat) (cause : BindError)
  | groupIndex (group : Nat)
  | groupRowLimit (group maximum actual : Nat)
  | read (group position ordinal : Nat) (cause : Int32ByteArrayGroup.Error)
  deriving DecidableEq, Repr

/-- Each projection entry retains a typed binding to the same checked snapshot. -/
inductive Bound (snapshot : Snapshot.Checked) where
  | int32 (name : String) (layout : FlatColumn.Layout)
      (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩)
  | byteArray (name : String) (layout : FlatColumn.Layout)
      (binding : FlatColumn.Binding snapshot ⟨name, .byteArray, layout⟩)

def Bound.selection {snapshot : Snapshot.Checked} : Bound snapshot → FlatColumn.Selection
  | .int32 name layout _ => ⟨name, .int32, layout⟩
  | .byteArray name layout _ => ⟨name, .byteArray, layout⟩

def Bound.binding {snapshot : Snapshot.Checked} (bound : Bound snapshot) :
    FlatColumn.Binding snapshot bound.selection :=
  match bound with
  | .int32 _ _ binding => binding
  | .byteArray _ _ binding => binding

def Bound.ordinal {snapshot : Snapshot.Checked} (bound : Bound snapshot) : Nat :=
  bound.binding.columnOrdinal

def Bound.field {snapshot : Snapshot.Checked} : Bound snapshot → Arrow.MixedFlat.Field
  | .int32 name layout _ => ⟨name, decide (layout.repetition = .optional), .primitive .int32⟩
  | .byteArray name layout _ => ⟨name, decide (layout.repetition = .optional), .view .binary⟩

private def bindLeaf (snapshot : Snapshot.Checked) (ordinal : Nat) : Except BindError (Bound snapshot) := do
  let some leaf := snapshot.metadata.schema[ordinal + 1]? | throw .missingLeaf
  let layout ← match leaf.repetition with
    | some .required => .ok FlatColumn.Layout.required
    | some .optional => .ok .optional
    | other => .error (.unsupportedLayout other)
  match leaf.physicalType with
  | some .int32 =>
    (FlatColumn.bindColumn snapshot ⟨leaf.name, .int32, layout⟩).map
      (Bound.int32 leaf.name layout) |>.mapError .binding
  | some .byteArray =>
    (FlatColumn.bindColumn snapshot ⟨leaf.name, .byteArray, layout⟩).map
      (Bound.byteArray leaf.name layout) |>.mapError .binding
  | other => .error (.unsupportedPhysical other)

/-- Resolve the original zero-based flat column ordinal and reuse exact typed binding. -/
def bindOrdinal (snapshot : Snapshot.Checked) (ordinal : Nat) : Except BindError (Bound snapshot) := do
  let bound ← bindLeaf snapshot ordinal
  if bound.ordinal = ordinal then .ok bound else .error (.ordinalMismatch bound.ordinal)

structure Checked where
  private mk ::
  snapshot : Snapshot.Checked
  columns : List (Bound snapshot)

def Checked.fields (checked : Checked) : List Arrow.MixedFlat.Field := checked.columns.map Bound.field

def bindProjection (snapshot : Snapshot.Checked) (ordinals : List Nat) : Except SourceError (List (Bound snapshot)) :=
  ordinals.zipIdx.mapM fun (ordinal, position) =>
    (bindOrdinal snapshot ordinal).mapError (.bind position ordinal)

/-- Bind in projection order before reading any group. Output names and
nullability come from the original checked leaves. -/
def openFile (limits : Limits) (input : Bytes) (ordinals : List Nat) : Except SourceError Checked := do
  if limits.column.maxFileBytes < input.length then
    throw (.fileByteLimit limits.column.maxFileBytes input.length)
  if limits.maxFields < ordinals.length then
    throw (.fieldLimit limits.maxFields ordinals.length)
  let snapshot ← (Snapshot.check limits.column.snapshot input).mapError .snapshot
  let rows := snapshot.metadata.numRows.toNat
  if limits.maxFileRows < rows then throw (.fileRowLimit limits.maxFileRows rows)
  let columns ← bindProjection snapshot ordinals
  return ⟨snapshot, columns⟩

def packBinary (slots : List (Option Bytes)) : List (Option KBytes) :=
  slots.map (Option.map fun bytes => Arrow.Writer.emitWords 1 (bytes.toList.map UInt8.toNat))

/-- Interpret the selected original chunk through the existing PLAIN decoder.
BYTE_ARRAY values stay opaque, including values with logical annotations. -/
def Bound.read {snapshot : Snapshot.Checked} (limits : Limits) (index : Nat) :
    Bound snapshot → Except Int32ByteArrayGroup.Error OrderedWriter.Column
  | .int32 name layout binding =>
    (FlatColumn.readColumn binding limits.column.column Plain.ByteArray.File.policy
      (Int32ByteArrayGroup.decodeInt32 limits.column layout) index).map
        (.int32 name (decide (layout.repetition = .optional))) |>.mapError .int32
  | .byteArray name layout binding =>
    (FlatColumn.readColumn binding limits.column.column Plain.ByteArray.File.policy
      (Int32ByteArrayGroup.decodeByteArray limits.column layout) index).map
        (fun slots => .binary name (decide (layout.repetition = .optional)) (packBinary slots)) |>.mapError .byteArray

/-- Wire evidence for one column includes the original page frames and the
exact flattened raw slots from their respective decoder. -/
def Bound.Wire {snapshot : Snapshot.Checked} (limits : Limits) (index : Nat)
    (group : Footer.RowGroup) (column : OrderedWriter.Column) : Bound snapshot → Prop
  | .int32 name layout binding =>
    ∃ slots, column = .int32 name (decide (layout.repetition = .optional)) slots ∧
      FlatColumn.ColumnWire binding limits.column.column
        (Int32ByteArrayGroup.decodeInt32 limits.column layout) index group slots
  | .byteArray name layout binding =>
    ∃ slots, column = .binary name (decide (layout.repetition = .optional)) (packBinary slots) ∧
      FlatColumn.ColumnWire binding limits.column.column
        (Int32ByteArrayGroup.decodeByteArray limits.column layout) index group slots

def readColumns {snapshot : Snapshot.Checked} (limits : Limits) (index : Nat)
    (columns : List (Bound snapshot)) : Except SourceError (List OrderedWriter.Column) :=
  columns.zipIdx.mapM fun (bound, position) =>
    (bound.read limits index).mapError (.read index position bound.ordinal)

/-- One complete batch per original footer group, including zero-row
groups. The group supplies the row count even for an empty projection. -/
def Checked.readGroup (limits : Limits) (index : Nat) (checked : Checked) :
    Except SourceError OrderedWriter.BatchInput := do
  let some group := checked.snapshot.groupAt index | throw (.groupIndex index)
  let rows := group.numRows.toNat
  if limits.column.column.maxRows < rows then throw (.groupRowLimit index limits.column.column.maxRows rows)
  let columns ← readColumns limits index checked.columns
  return ⟨rows, columns⟩

def Checked.indices (checked : Checked) : List Nat := List.range checked.snapshot.groupCount

def Checked.readAll (limits : Limits) (checked : Checked) : Except SourceError (List OrderedWriter.BatchInput) :=
  checked.indices.mapM fun index => checked.readGroup limits index

inductive Error where
  | source (cause : SourceError)
  | writer (cause : OrderedWriter.Error)
  deriving DecidableEq, Repr

/-- Exhaust the selected source before emitting a carrier. A footer with
zero groups produces a schema-only stream. An explicit empty group still
produces a RecordBatch. -/
def convert (parquet : Limits) (ipc : Arrow.MixedFlat.Limits) (input : Bytes)
    (ordinals : List Nat) : Except Error KBytes := do
  let checked ← (openFile parquet input ordinals).mapError .source
  let batches ← (checked.readAll parquet).mapError .source
  (OrderedWriter.emit ipc checked.fields batches).mapError .writer

end Silmaril.Formats.Parquet.FlatProjection
