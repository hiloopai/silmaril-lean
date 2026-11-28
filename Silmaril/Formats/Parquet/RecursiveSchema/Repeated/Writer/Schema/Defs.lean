module

public import Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.Defs
public import Silmaril.Formats.Parquet.ListFile.Writer.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Defs

/-! An opt-in inverse for the signed recursive Parquet declaration profile. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema

open RecursiveSchema (Kind)

@[expose] public section

inductive Entry where
  | leaf (name : String) (nullable : Bool) (kind : Kind)
  | struct (name : String) (nullable : Bool) (children : Nat)
  | list (name : String) (nullable : Bool)
  | wrapper
  deriving DecidableEq, Repr

def repetition (nullable : Bool) : Footer.Repetition :=
  if nullable then .optional else .required

def Entry.element : Entry → Footer.SchemaElement
  | .leaf name nullable kind => ⟨some kind.physical, none, some (repetition nullable), name, none⟩
  | .struct name nullable children => ⟨none, none, some (repetition nullable), name, some children⟩
  | .list name nullable => ⟨none, none, some (repetition nullable), name, some 1⟩
  | .wrapper => ⟨none, none, some .repeated, "list", some 1⟩

structure Plan where
  roots : Nat
  entries : List Entry

def Plan.schema (plan : Plan) : List Footer.SchemaElement :=
  FlatInt32Writer.Compact.schemaRoot plan.roots :: plan.entries.map Entry.element

structure Limits where
  snapshot : Snapshot.Limits := {}
  maxFields : Nat := 4096
  maxFileBytes : Nat := 256 * 1024 * 1024

def Limits.fileBytes (limits : Limits) : Nat := min limits.maxFileBytes (2^63 - 1)

inductive Error where
  | emptyRoot
  | depth (parent : List String)
  | fieldLimit
  | missingName (parent : List String)
  | nameBudget (path : List String)
  | duplicate (path : List String)
  | arity (path : List String) (kind : Arrow.RecursiveSchema.Wire.Kind) (count : Nat)
  | nestedList (path : List String)
  | fileLimit
  | compact (cause : FlatInt32Writer.Compact.Error)
  | openReadback (cause : Repeated.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

def planSiblings (parent : List String)
    (visit : Arrow.RecursiveSchema.Field → Nat → Except Error (List Entry × Nat))
    (fields : List Arrow.RecursiveSchema.Field) (remaining : Nat) : Except Error (List Entry × Nat) :=
  go fields remaining {}
where
  go : List Arrow.RecursiveSchema.Field → Nat → Std.HashSet String → Except Error (List Entry × Nat)
    | [], remaining, _ => .ok ([], remaining)
    | field@(.node name _ _ _) :: rest, remaining, names => do
      let some name := name | throw (.missingName parent)
      if names.contains name then throw (.duplicate (parent ++ [name]))
      let (first, remaining) ← visit field remaining
      let (tail, remaining) ← go rest remaining (names.insert name)
      return (first ++ tail, remaining)

def planFieldWith (nameBytes : Nat) (allowNested : Bool) :
    Nat → Bool → List String → Arrow.RecursiveSchema.Field → Nat → Except Error (List Entry × Nat)
  | 0, _, parent, _, _ => .error (.depth parent)
  | _ + 1, _, _, _, 0 => .error .fieldLimit
  | depth + 1, repeated, parent, .node name nullable kind children, remaining + 1 => do
    let some name := name | throw (.missingName parent)
    let path := parent ++ [name]
    if name.utf8ByteSize > nameBytes then throw (.nameBudget path)
    match kind with
    | .int32 | .int64 =>
      if !children.isEmpty then throw (.arity path kind children.length)
      return ([.leaf name nullable (if kind == .int32 then .int32 else .int64)], remaining)
    | .struct =>
      if children.isEmpty then throw (.arity path kind 0)
      let (entries, remaining) ← planSiblings path (planFieldWith nameBytes allowNested depth repeated path)
        children remaining
      return (.struct name nullable children.length :: entries, remaining)
    | .list =>
      if repeated && !allowNested then throw (.nestedList path)
      let [child] := children | throw (.arity path kind children.length)
      let depth + 1 := depth | throw (.depth path)
      let remaining + 1 := remaining | throw .fieldLimit
      let (entries, remaining) ← planFieldWith nameBytes allowNested depth true (path ++ ["list"]) child remaining
      return (.list name nullable :: .wrapper :: entries, remaining)

def planField (nameBytes : Nat) := planFieldWith nameBytes false

def planWith (limits : Limits) (allowNested : Bool) (schema : Arrow.RecursiveSchema.Schema) : Except Error Plan := do
  if schema.fields.isEmpty then throw .emptyRoot
  let compact := limits.snapshot.footer.compact
  let names := compact.maxBinaryBytes
  if names < "schema".utf8ByteSize then throw (.nameBudget [])
  let budget := min limits.maxFields compact.maxCollectionSize
  if budget = 0 then throw .fieldLimit
  let (entries, _) ← planSiblings [] (planFieldWith names allowNested (limits.snapshot.maxSchemaDepth - 1) false [])
    schema.fields (budget - 1)
  return ⟨schema.fields.length, entries⟩

def plan (limits : Limits) (schema : Arrow.RecursiveSchema.Schema) : Except Error Plan :=
  planWith limits false schema

/-- Only actual emitted chunk extents are supplied by the file writer. -/
structure ColumnIndex where
  kind : Kind
  path : List String
  slots : Nat
  dataPageOffset : Nat
  size : Nat

def ColumnIndex.metadata (column : ColumnIndex) : Footer.ColumnChunk :=
  ⟨0, ⟨column.kind.physical, [0, 3], column.path, 0, column.slots, column.size, column.size,
    column.dataPageOffset, none, none, none, none⟩, none, none, none, none⟩

structure GroupIndex where
  rows : Nat
  columns : List ColumnIndex

def GroupIndex.size (group : GroupIndex) : Nat := (group.columns.map (·.size)).sum

def GroupIndex.metadata (group : GroupIndex) : Footer.RowGroup :=
  ⟨group.columns.map ColumnIndex.metadata, group.size, group.rows, none, none⟩

def metadata (schema : Plan) (groups : List GroupIndex) : Footer.Metadata :=
  ⟨1, schema.schema, (groups.map (·.rows)).sum, groups.map GroupIndex.metadata, none⟩

namespace Compact

open FlatInt32Writer.Compact (Write field integer octet text listHeader root)

def entry : Entry → Write Unit
  | .leaf name nullable kind =>
    NestedPoint.Multi.Writer.Compact.leaf (if kind = .int32 then 1 else 2) nullable name
  | .wrapper => ListFile.Writer.Compact.repeatedGroup
  | .struct name nullable children => do
    field 3 5
    integer .i32 (if nullable then 1 else 0)
    field 1 8
    text name
    field 1 5
    integer .i32 children
    octet 0
  | .list name nullable => do
    field 3 5
    integer .i32 (if nullable then 1 else 0)
    field 1 8
    text name
    field 1 5
    integer .i32 1
    field 1 5
    integer .i32 3
    field 4 12
    field 3 12
    octet 0
    octet 0
    octet 0

def chunk (column : ColumnIndex) : Write Unit := do
  field 2 6
  integer .i64 0
  field 1 12
  field 1 5
  integer .i32 (if column.kind = .int32 then 1 else 2)
  field 1 9
  listHeader 5 2
  integer .i32 0
  integer .i32 3
  field 1 9
  listHeader 8 column.path.length
  for name in column.path do text name
  field 1 5
  integer .i32 0
  field 1 6
  integer .i64 column.slots
  field 1 6
  integer .i64 column.size
  field 1 6
  integer .i64 column.size
  field 2 6
  integer .i64 column.dataPageOffset
  octet 0
  octet 0

def group (index : GroupIndex) : Write Unit := do
  field 1 9
  listHeader 12 index.columns.length
  for column in index.columns do chunk column
  field 1 6
  integer .i64 index.size
  field 1 6
  integer .i64 index.rows
  octet 0

def footer (schema : Plan) (groups : List GroupIndex) : Write Unit := do
  field 1 5
  integer .i32 1
  field 1 9
  listHeader 12 (schema.entries.length + 1)
  root schema.roots
  for item in schema.entries do entry item
  field 1 6
  integer .i64 (groups.map (·.rows)).sum
  field 1 9
  listHeader 12 groups.length
  for index in groups do group index
  octet 0

def encode (cap : Nat) (schema : Plan) (groups : List GroupIndex) :
    Except FlatInt32Writer.Compact.Error Bytes :=
  ((footer schema groups).run ⟨cap, .empty⟩).map (·.2.bytes)

end Compact

structure Envelope where
  bytes : Bytes
  footer : Footer.Span

def footerCap (limits : Limits) (start : Nat) : Nat :=
  min limits.snapshot.footer.maxFooterBytes (min (2^32 - 1) (limits.fileBytes - start - 8))

/-- Assemble the ordinary PAR1 envelope with a bounded Compact footer. -/
def wrap (limits : Limits) (payload : Bytes) (schema : Plan) (groups : List GroupIndex) :
    Except Error Envelope := do
  let start := 4 + payload.length
  if start + 8 > limits.fileBytes then throw .fileLimit
  let footer ← (Compact.encode (footerCap limits start) schema groups).mapError .compact
  let bytes := (((Footer.magic.append payload).append footer).append
    (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic
  return ⟨bytes, ⟨start, start + footer.length⟩⟩

structure Checked (limits : Limits) where
  plan : Plan
  envelope : Envelope
  source : Repeated.Source limits.snapshot envelope.bytes

def equal (depth : Nat) (left right : Arrow.RecursiveSchema.Schema) : Bool :=
  Arrow.RecursiveSchema.Writer.equalFields (Arrow.RecursiveSchema.Writer.equalField depth)
    left.fields right.fields

/-- Obtain the leaf plans from the existing compiler on actual schema-only
Parquet bytes. Those same planned schema entries are used in the final footer. -/
def emit (limits : Limits) (schema : Arrow.RecursiveSchema.Schema) :
    Except Error (Checked limits) := do
  let declared ← plan limits schema
  let envelope ← wrap limits .empty declared []
  let source ← (Repeated.openFile limits.snapshot envelope.bytes).mapError .openReadback
  if equal limits.snapshot.maxSchemaDepth schema source.schema.arrow &&
      decide (source.snapshot.footer = envelope.footer ∧ source.snapshot.metadata = metadata declared [] ∧
        source.snapshot.groupCount = 0) then
    return ⟨declared, envelope, source⟩
  else throw .readbackMismatch

structure Wire (limits : Limits) (schema : Arrow.RecursiveSchema.Schema)
    (output : Checked limits) : Prop where
  planned : plan limits schema = .ok output.plan
  framed : wrap limits .empty output.plan [] = .ok output.envelope
  opened : Repeated.openFile limits.snapshot output.envelope.bytes = .ok output.source
  declaration : output.source.schema.arrow = schema
  footer : output.source.snapshot.footer = output.envelope.footer
  metadata : output.source.snapshot.metadata = metadata output.plan []
  groups : output.source.snapshot.groupCount = 0

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema
