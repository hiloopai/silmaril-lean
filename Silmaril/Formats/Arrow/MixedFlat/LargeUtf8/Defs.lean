module

public import Silmaril.Formats.Arrow.MixedFlat.Defs
public import Silmaril.Formats.Arrow.LargeUtf8.Defs

/-! Opt-in mixed-flat RecordBatch decoding with signed i64 LargeUtf8 offsets. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.LargeUtf8

inductive Column where
  | existing (values : MixedFlat.Column)
  | largeUtf8 (values : Arrow.LargeUtf8.Column)

inductive ColumnError where
  | layout
  | existing (cause : MixedFlat.ColumnError)
  | largeUtf8 (cause : Arrow.LargeUtf8.Error)
  deriving DecidableEq, Repr

inductive Error where
  | schema (cause : Arrow.Error)
  | metadata (cause : MetadataError)
  | binding (cause : MixedFlat.Error)
  | field (index : Nat) (cause : ColumnError)
  deriving DecidableEq, Repr

structure Observed where
  rowCount : Nat
  columns : List (Field × Column)

def readMetadata (limits : MixedFlat.Limits) (fields : List Field) (bytes : KBytes) :
    Except MetadataError Metadata :=
  MixedFlat.readMetadata limits.observation.ipc limits.view.dataBuffers limits.totalDataBuffers
    (fields.map Field.layout) bytes

def readColumn (limits : MixedFlat.Limits) (body : KBytes) (field : Field) {rows : Nat}
    (group : Group rows) : Except ColumnError Column := do
  match field.kind with
  | .existing _ => (MixedFlat.readGroup limits.view body group).mapError .existing |>.map .existing
  | .largeUtf8 =>
    let [validity, offsets, data] := group.buffers | throw .layout
    let buffers : Binary.Buffers :=
      ⟨Body.sliceBuffer body validity, Body.sliceBuffer body offsets, Body.sliceBuffer body data⟩
    (Arrow.LargeUtf8.readColumn limits.observation.ipc field.nullable group.node buffers)
      |>.mapError .largeUtf8 |>.map .largeUtf8

def readColumns (limits : MixedFlat.Limits) (body : KBytes) {rows : Nat} :
    Nat → List (Field × Group rows) → Except Error (List (Field × Column))
  | _, [] => .ok []
  | index, (field, group) :: groups => do
    let column ← (readColumn limits body field group).mapError (.field index)
    let rest ← readColumns limits body (index + 1) groups
    return (field, column) :: rest

/-- Bind the complete original descriptor vector before slicing columns.
Keep the wire type separate from its layout throughout value decoding. -/
def readParsed (limits : MixedFlat.Limits) (fields : List Field) (metadata : Metadata) (body : KBytes) :
    Except Error Observed := do
  let plan ← (MixedFlat.bindBatch limits (fields.map Field.layout) metadata body).mapError .binding
  let columns ← readColumns limits body 0 (fields.zip plan.assignment.groups)
  return ⟨metadata.batch.rowCount, columns⟩

def readBatch (limits : MixedFlat.Limits) (schemaBytes recordBytes body : KBytes) :
    Except Error Observed := do
  let fields ← (readSchema limits.observation.ipc schemaBytes).mapError .schema
  let metadata ← (readMetadata limits fields recordBytes).mapError .metadata
  readParsed limits fields metadata body

/-- The declaration and decoded value use the same position in the
assigned node and descriptor groups. -/
def ColumnWire (limits : MixedFlat.Limits) (body : KBytes) {rows : Nat}
    (assigned : Field × Group rows) (column : Field × Column) : Prop :=
  column.1 = assigned.1 ∧ readColumn limits body assigned.1 assigned.2 = .ok column.2

structure BatchWire (limits : MixedFlat.Limits) (fields : List Field) (metadata : Metadata)
    (body : KBytes) (observed : Observed) : Prop where
  bound : ∃ plan : Plan (fields.map Field.layout) metadata body,
    MixedFlat.bindBatch limits (fields.map Field.layout) metadata body = .ok plan ∧
    observed.rowCount = metadata.batch.rowCount ∧
    List.Forall₂ (fun field group => group.field = field.layout) fields plan.assignment.groups ∧
    List.Forall₂ (ColumnWire limits body) (fields.zip plan.assignment.groups) observed.columns

end Silmaril.Formats.Arrow.MixedFlat.LargeUtf8
