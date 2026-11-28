module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.Defs

/-! Checked PLAIN V1/V2 groups with two signed columns sharing two
recursive LIST wrappers and independently selected bounded ListPath codecs. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader

open RecursiveSchema.Chunk (Address)
open Arrow.RecursiveSchema.Batch.Rows (Observation)

@[expose] public section

abbrev Limits := ListPath.Chunk.Limits

def address (plan : Plan) (group : Nat) (side : Side) : Address :=
  ⟨group, side.column, (plan.child side).1.location.path⟩

inductive BindError where
  | group (ordinal : Nat)
  | columns (ordinal actual : Nat)
  | rowCount (group : Nat) (actual : Int)
  | column (address : Address) (cause : ListPath.Chunk.BindCause)
  deriving DecidableEq, Repr

structure GroupBinding (snapshot : Snapshot.Checked) (group : Nat) where
  original : Footer.RowGroup
  groupAt : snapshot.groupAt group = some original
  columns : original.columns.length = 2
  rows : 0 ≤ original.numRows

structure ColumnBinding {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {group : Nat} (bound : GroupBinding snapshot group) (side : Side) where
  column : Footer.ColumnChunk
  span : Footer.Span
  columnAt : bound.original.columns[side.column]? = some column
  path : column.metadata.pathInSchema = (schema.plan.child side).1.location.path
  physical : column.metadata.physicalType = (schema.plan.child side).2.physical
  codec : ListPath.Chunk.Codec
  originalCodec : ListPath.Chunk.Codec.ofId column.metadata.codec = some codec
  plain : RecursiveSchema.SupportedEncodings column.metadata
  offsets : column.metadata.dictionaryPageOffset = none ∧ column.metadata.indexPageOffset = none
  unindexed : Repeated.Chunk.Unindexed column
  slots : 0 ≤ column.metadata.numValues
  originalSpan : Page.columnSpan snapshot.footer.start column.metadata = some span

def carrierOf {limits : Snapshot.Limits} {snapshot : Snapshot.Checked} {schema : Compiled limits snapshot}
    {group : Nat} {bound : GroupBinding snapshot group} {side : Side}
    (binding : ColumnBinding schema bound side) : ListPath.Chunk.Carrier :=
  ⟨schema.plan.path side, snapshot.bytes, binding.span, address schema.plan group side,
    binding.column.metadata.numValues.toNat, bound.original.numRows.toNat,
    binding.column.metadata.totalCompressedSize, binding.column.metadata.totalUncompressedSize,
    binding.codec, binding.column.metadata⟩

end

private def lookup {α ε : Type} (option : Option α) (error : ε) :
    Except ε {value // option = some value} :=
  match option with
  | none => .error error
  | some value => .ok ⟨value, rfl⟩

private def guard {ε : Type} (condition : Prop) [Decidable condition] (error : ε) : Except ε (PLift condition) :=
  if yes : condition then .ok ⟨yes⟩ else .error error

public def bindGroup (snapshot : Snapshot.Checked) (group : Nat) : Except BindError (GroupBinding snapshot group) := do
  let ⟨original, groupAt⟩ ← lookup (snapshot.groupAt group) (.group group)
  let ⟨columns⟩ ← guard (original.columns.length = 2) (.columns group original.columns.length)
  let ⟨rows⟩ ← guard (0 ≤ original.numRows) (.rowCount group original.numRows)
  return ⟨original, groupAt, columns, rows⟩

public def bindColumn {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) {group : Nat} (bound : GroupBinding snapshot group) (side : Side) :
    Except BindError (ColumnBinding schema bound side) := do
  let fail := BindError.column (address schema.plan group side)
  let ⟨column, columnAt⟩ ← lookup bound.original.columns[side.column]? (fail (.columns bound.original.columns.length))
  let metadata := column.metadata
  let child := schema.plan.child side
  let ⟨⟨path, physical⟩⟩ ← guard
    (metadata.pathInSchema = child.1.location.path ∧ metadata.physicalType = child.2.physical) (fail .association)
  let ⟨codec, originalCodec⟩ ← lookup (ListPath.Chunk.Codec.ofId metadata.codec) (fail (.codec metadata.codec))
  let ⟨plain⟩ ← guard (RecursiveSchema.SupportedEncodings metadata) (fail (.encodings metadata.encodings))
  let ⟨offsets⟩ ← guard
    (metadata.dictionaryPageOffset = none ∧ metadata.indexPageOffset = none) (fail .pageOffsets)
  let ⟨unindexed⟩ ← guard (Repeated.Chunk.Unindexed column) (fail .pageIndex)
  let ⟨slots⟩ ← guard (0 ≤ metadata.numValues) (fail .counts)
  let ⟨span, originalSpan⟩ ← lookup (Page.columnSpan snapshot.footer.start metadata) (fail .span)
  return ⟨column, span, columnAt, path, physical, codec, originalCodec, plain, offsets, unindexed, slots, originalSpan⟩

@[expose] public section

def readColumn {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {bound : GroupBinding snapshot group} {side : Side}
    (limits : Limits) (binding : ColumnBinding schema bound side) : Except ListPath.Chunk.Error ListPath.Chunk.Observation :=
  let carrier := carrierOf binding
  ListPath.Chunk.readCarrier limits carrier (.plain binding.plain binding.offsets.1) (fun _ => .ok ())

inductive Error where
  | binding (cause : BindError)
  | chunk (cause : ListPath.Chunk.Error)
  | topology (cause : Rows.TopologyError)
  | child (column : Address) (cause : ListPath.Rows.Error)
  | reconstruction (group : Nat)
  deriving DecidableEq, Repr

/-- Decode both original chunks before comparing their addressed slots.
The logical rows come from the two checked LIST-path reconstructions. -/
def readGroup {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (schema : Compiled schemaLimits snapshot) (group : Nat) : Except Error Observation := do
  let bound ← (bindGroup snapshot group).mapError .binding
  let left ← (bindColumn schema bound .left).mapError .binding
  let right ← (bindColumn schema bound .right).mapError .binding
  let leftOriginal ← (readColumn limits left).mapError .chunk
  let rightOriginal ← (readColumn limits right).mapError .chunk
  let plan := schema.plan
  let leftAddress := address plan group .left
  let rightAddress := address plan group .right
  let lhs := Rows.addressed leftAddress leftOriginal
  let rhs := Rows.addressed rightAddress rightOriginal
  (Rows.checkTopology plan.sharedDefinition leftAddress rightAddress lhs rhs 0).mapError .topology
  let count := bound.original.numRows.toNat
  let leftRows ← (ListPath.Rows.reconstruct limits.logical (plan.path .left) count leftOriginal.atoms).mapError
    (.child leftAddress)
  let rightRows ← (ListPath.Rows.reconstruct limits.logical (plan.path .right) count rightOriginal.atoms).mapError
    (.child rightAddress)
  let some rows := Rows.mergeRows leftRows.rows rightRows.rows plan.element.nullable | throw (.reconstruction group)
  return ⟨count, rows⟩

def readAll {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (schema : Compiled schemaLimits snapshot) : Except Error (List Observation) :=
  (List.range snapshot.groupCount).mapM (readGroup limits schema)

structure ColumnWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {bound : GroupBinding snapshot group} {side : Side}
    (limits : Limits) (binding : ColumnBinding schema bound side) (observed : ListPath.Chunk.Observation) : Prop where
  original : ListPath.Chunk.Wire limits (carrierOf binding) observed
  dictionaryFree : observed.dictionary = none

structure GroupWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (schema : Compiled schemaLimits snapshot) (group : Nat) (out : Observation) : Prop where
  original : ∃ (bound : GroupBinding snapshot group) (left : ColumnBinding schema bound .left)
      (right : ColumnBinding schema bound .right) (lhs rhs : ListPath.Chunk.Observation),
    ColumnWire limits left lhs ∧ ColumnWire limits right rhs ∧
    out.rowCount = bound.original.numRows.toNat ∧ out.rows.length = out.rowCount ∧
    Rows.TopologyWire schema.plan.sharedDefinition
      (Rows.addressed (address schema.plan group .left) lhs)
      (Rows.addressed (address schema.plan group .right) rhs) ∧
    (∀ side, ∃ rows,
      Rows.projectRows side out.rows schema.plan.element.nullable = some rows ∧
      ListPath.Rows.Relation (schema.plan.path side) (side.select lhs rhs).atoms rows)

structure GroupTopologyFailure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (schema : Compiled schemaLimits snapshot) (group : Nat)
    (cause : Rows.TopologyError) : Prop where
  original : ∃ (bound : GroupBinding snapshot group) (left : ColumnBinding schema bound .left)
      (right : ColumnBinding schema bound .right) (lhs rhs : ListPath.Chunk.Observation),
    ColumnWire limits left lhs ∧ ColumnWire limits right rhs ∧
    Rows.TopologyFailure schema.plan.sharedDefinition (address schema.plan group .left)
      (address schema.plan group .right) (Rows.addressed (address schema.plan group .left) lhs)
      (Rows.addressed (address schema.plan group .right) rhs) 0 cause

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader
