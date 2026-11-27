module

public import Silmaril.Formats.Parquet.Footer.NestedLeaf.Defs
public import Silmaril.Formats.Parquet.Page.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Defs

/-! Compile one checked Parquet footer into non-repeated signed nested
fields and ordered definition-level plans. Page payload reading is separate. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema

@[expose] public section

structure Location where
  /-- Zero-based ordinal in the original flattened schema, including the root. -/
  ordinal : Nat
  path : List String
  deriving DecidableEq, Repr

structure Site where
  location : Location
  name : String
  nullable : Bool
  deriving DecidableEq, Repr

inductive Kind where
  | int32 | int64
  deriving DecidableEq, Repr

def Kind.physical : Kind → Footer.PhysicalType
  | .int32 => .int32
  | .int64 => .int64

def Kind.arrow : Kind → Arrow.RecursiveSchema.Wire.Kind
  | .int32 => .int32
  | .int64 => .int64

structure Leaf where
  site : Site
  kind : Kind
  /-- Optional ancestor positions in order, followed by the leaf if optional. -/
  optional : List Location
  deriving DecidableEq, Repr

def Leaf.maxDefinition (leaf : Leaf) : Nat := leaf.optional.length

def Leaf.bitWidth (leaf : Leaf) : Nat :=
  if leaf.maxDefinition = 0 then 0 else leaf.maxDefinition.log2 + 1

inductive Presence where
  | absent (location : Location)
  | value
  deriving DecidableEq, Repr

inductive DefinitionError where
  | level (leaf : Location) (row actual maximum : Nat)
  deriving DecidableEq, Repr

/-- Level k means k optional declarations were reached. The next optional
declaration is absent unless k is the maximum, when a signed word is present. -/
def Leaf.classify (leaf : Leaf) (row level : Nat) : Except DefinitionError Presence :=
  if level = leaf.maxDefinition then .ok .value else
    match leaf.optional[level]? with
    | some missing => .ok (.absent missing)
    | none => .error (.level leaf.site.location row level leaf.maxDefinition)

inductive Field where
  | group (site : Site) (children : List Field)
  | leaf (plan : Leaf)
  deriving Repr

def Field.leaves : Field → List Leaf
  | .group _ children => children.flatMap Field.leaves
  | .leaf plan => [plan]

def Field.arrow : Field → Arrow.RecursiveSchema.Field
  | .group site children =>
    .node (some site.name) site.nullable .struct (children.map Field.arrow)
  | .leaf plan => .node (some plan.site.name) plan.site.nullable plan.kind.arrow []

inductive Error where
  | snapshot (original : Snapshot.Error Unit)
  | footerItems (original : Footer.NestedLeaf.Error)
  | schemaExtent (expected actual : Nat)
  | root
  | missing (location : Location)
  | depth (location : Location)
  | repetition (location : Location) (original : Option Footer.Repetition)
  | annotation (location : Location)
  | typeLength (location : Location)
  | arity (location : Location) (original : Option Int)
  | physical (location : Location) (original : Footer.PhysicalType)
  | trailing (ordinal : Nat)
  deriving DecidableEq, Repr

abbrev Entry := Footer.SchemaElement × Footer.ColumnOrder.Item

def entries (snapshot : Snapshot.Checked) (items : List Footer.ColumnOrder.Item) : Array Entry :=
  (snapshot.metadata.schema.zip items).toArray

def Unannotated (entry : Entry) : Prop :=
  entry.2.fields.all (fun field => field.id != 6 && field.id != 10) = true

instance (entry : Entry) : Decidable (Unannotated entry) := by
  unfold Unannotated
  infer_instance

def RepetitionWire (entry : Entry) (nullable : Bool) : Prop :=
  entry.1.repetition = some (if nullable then .optional else .required)

structure Context where
  path : List String := []
  optional : List Location := []

def Context.site (ctx : Context) (ordinal : Nat) (name : String) (nullable : Bool) : Site :=
  ⟨⟨ordinal, ctx.path ++ [name]⟩, name, nullable⟩

def Context.enter (ctx : Context) (site : Site) : Context :=
  ⟨site.location.path, if site.nullable then ctx.optional ++ [site.location] else ctx.optional⟩

mutual

/-- A field consumes its original schema item and, for a group, exactly
its original declared children. The path excludes the root and the
optional sequence is accumulated along that path. -/
inductive FieldWire (original : Array Entry) : Nat → Context → Nat → Field → Nat → Prop where
  | leaf {depth ctx ordinal entry nullable kind} :
      original[ordinal]? = some entry →
      Unannotated entry → RepetitionWire entry nullable → entry.1.typeLength = none →
      entry.1.physicalType = some kind.physical → entry.1.numChildren.getD 0 = 0 →
      FieldWire original (depth + 1) ctx ordinal
        (.leaf ⟨ctx.site ordinal entry.1.name nullable, kind,
          (ctx.enter (ctx.site ordinal entry.1.name nullable)).optional⟩) (ordinal + 1)
  | group {depth ctx ordinal entry nullable count children next} :
      original[ordinal]? = some entry →
      Unannotated entry → RepetitionWire entry nullable → entry.1.typeLength = none →
      entry.1.physicalType = none → entry.1.numChildren = some count → 0 < count →
      FieldsWire original depth (ctx.enter (ctx.site ordinal entry.1.name nullable))
        count.toNat (ordinal + 1) children next →
      FieldWire original (depth + 1) ctx ordinal
        (.group (ctx.site ordinal entry.1.name nullable) children) next

inductive FieldsWire (original : Array Entry) :
    Nat → Context → Nat → Nat → List Field → Nat → Prop where
  | nil {depth ctx ordinal} : FieldsWire original depth ctx 0 ordinal [] ordinal
  | cons {depth ctx count ordinal field more middle next} :
      FieldWire original depth ctx ordinal field middle →
      FieldsWire original depth ctx count middle more next →
      FieldsWire original depth ctx (count + 1) ordinal (field :: more) next

end

structure RootWire (original : Array Entry) (depth : Nat) (root : Entry) (fields : List Field) : Prop where
  originalRoot : original[0]? = some root
  unannotated : Unannotated root
  group : root.1.physicalType = none ∧ root.1.typeLength = none
  repetition : root.1.repetition = none ∨ root.1.repetition = some .required
  children : ∃ count, root.1.numChildren = some count ∧ 0 < count ∧
    FieldsWire original depth {} count.toNat 1 fields original.size

structure Compiled (limits : Snapshot.Limits) (snapshot : Snapshot.Checked) where
  container : ThriftCompact.Traversal.Field
  items : List Footer.ColumnOrder.Item
  root : Entry
  fields : List Field
  leaves : Array Leaf
  originalItems : Footer.NestedLeaf.readItems limits.footer snapshot = .ok (container, items)
  aligned : snapshot.metadata.schema.length = items.length
  grammar : RootWire (entries snapshot items) (limits.maxSchemaDepth - 1) root fields
  ordered : leaves = (fields.flatMap Field.leaves).toArray

structure Source (limits : Snapshot.Limits) (bytes : Bytes) where
  snapshot : Snapshot.Checked
  schema : Compiled limits snapshot
  original : Snapshot.check (Failure := Unit) limits bytes = .ok snapshot

def Compiled.arrow {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) : Arrow.RecursiveSchema.Schema :=
  ⟨schema.fields.map Field.arrow⟩

end

private def witness {ε α : Type} (result : Except ε α) : Except ε {value // result = .ok value} :=
  match result with
  | .ok value => .ok ⟨value, rfl⟩
  | .error cause => .error cause

private def entryAt (original : Array Entry) (ordinal : Nat) (missing : Error) :
    Except Error {value // original[ordinal]? = some value} :=
  match original[ordinal]? with
  | none => .error missing
  | some entry => .ok ⟨entry, rfl⟩

private def checkRepetition (entry : Entry) (location : Location) :
    Except Error {nullable // RepetitionWire entry nullable} :=
  match found : entry.1.repetition with
  | some .required => .ok ⟨false, found⟩
  | some .optional => .ok ⟨true, found⟩
  | other => .error (.repetition location other)

private structure FieldResult (original : Array Entry) (depth : Nat) (ctx : Context) (ordinal : Nat) where
  field : Field
  next : Nat
  wire : FieldWire original depth ctx ordinal field next

private structure FieldsResult (original : Array Entry) (depth : Nat) (ctx : Context) (count ordinal : Nat) where
  fields : List Field
  next : Nat
  wire : FieldsWire original depth ctx count ordinal fields next

private def readFields (original : Array Entry) (depth : Nat) (ctx : Context)
    (readField : (ordinal : Nat) → Except Error (FieldResult original depth ctx ordinal)) :
    (count ordinal : Nat) → Except Error (FieldsResult original depth ctx count ordinal)
  | 0, ordinal => .ok ⟨[], ordinal, .nil⟩
  | count + 1, ordinal => do
    let first ← readField ordinal
    let tail ← readFields original depth ctx readField count first.next
    return ⟨first.field :: tail.fields, tail.next, .cons first.wire tail.wire⟩

private def readField (original : Array Entry) :
    (depth : Nat) → (ctx : Context) → (ordinal : Nat) →
      Except Error (FieldResult original depth ctx ordinal)
  | 0, ctx, ordinal => do
    let entry ← entryAt original ordinal (.missing ⟨ordinal, ctx.path⟩)
    throw (.depth (ctx.site ordinal entry.val.1.name false).location)
  | depth + 1, ctx, ordinal => do
    let ⟨entry, atOrdinal⟩ ← entryAt original ordinal (.missing ⟨ordinal, ctx.path⟩)
    let location := (ctx.site ordinal entry.1.name false).location
    if unannotated : Unannotated entry then
      if natural : entry.1.typeLength = none then
        let ⟨nullable, repetition⟩ ← checkRepetition entry location
        let site := ctx.site ordinal entry.1.name nullable
        let childContext := ctx.enter site
        match physical : entry.1.physicalType with
        | none =>
          match count : entry.1.numChildren with
          | none => throw (.arity location none)
          | some children =>
            if positive : 0 < children then
              let parsed ← readFields original depth childContext
                (readField original depth childContext) children.toNat (ordinal + 1)
              return ⟨.group site parsed.fields, parsed.next,
                .group atOrdinal unannotated repetition natural physical count positive parsed.wire⟩
            else throw (.arity location (some children))
        | some type =>
          if terminal : entry.1.numChildren.getD 0 = 0 then
            match kind : type with
            | .int32 =>
              return ⟨.leaf ⟨site, .int32, childContext.optional⟩, ordinal + 1,
                .leaf atOrdinal unannotated repetition natural (physical.trans (congrArg some kind)) terminal⟩
            | .int64 =>
              return ⟨.leaf ⟨site, .int64, childContext.optional⟩, ordinal + 1,
                .leaf atOrdinal unannotated repetition natural (physical.trans (congrArg some kind)) terminal⟩
            | other => throw (.physical location other)
          else throw (.arity location entry.1.numChildren)
      else throw (.typeLength location)
    else throw (.annotation location)

private def readRoot (original : Array Entry) (depth : Nat) :
    Except Error {value : Entry × List Field // RootWire original depth value.1 value.2} := do
  let ⟨root, atRoot⟩ ← entryAt original 0 .root
  if unannotated : Unannotated root then
    if group : root.1.physicalType = none ∧ root.1.typeLength = none then
      if repetition : root.1.repetition = none ∨ root.1.repetition = some .required then
        match count : root.1.numChildren with
        | none => throw .root
        | some children =>
          if positive : 0 < children then
            let fields ← readFields original depth {} (readField original depth {}) children.toNat 1
            if exactEnd : fields.next = original.size then
              return ⟨(root, fields.fields), ⟨atRoot, unannotated, group, repetition,
                children, count, positive, exactEnd ▸ fields.wire⟩⟩
            else throw (.trailing fields.next)
          else throw .root
      else throw .root
    else throw .root
  else throw (.annotation ⟨0, []⟩)

/-- Read the raw SchemaElement vector once for annotation admission and
pair each original item with the checked typed element at its ordinal. -/
public def compile (limits : Snapshot.Limits) (snapshot : Snapshot.Checked) :
    Except Error (Compiled limits snapshot) := do
  let ⟨(container, items), found⟩ ←
    witness ((Footer.NestedLeaf.readItems limits.footer snapshot).mapError .footerItems)
  have originalItems : Footer.NestedLeaf.readItems limits.footer snapshot = .ok (container, items) := by
    cases original : Footer.NestedLeaf.readItems limits.footer snapshot <;>
      simp [original, Except.mapError] at found ⊢
    exact found
  if aligned : snapshot.metadata.schema.length = items.length then
    let ⟨(root, fields), grammar⟩ ← readRoot (entries snapshot items) (limits.maxSchemaDepth - 1)
    return ⟨container, items, root, fields, (fields.flatMap Field.leaves).toArray,
      originalItems, aligned, grammar, rfl⟩
  else throw (.schemaExtent snapshot.metadata.schema.length items.length)

public def openFile (limits : Snapshot.Limits) (bytes : Bytes) : Except Error (Source limits bytes) := do
  let ⟨snapshot, opened⟩ ← witness ((Snapshot.check (Failure := Unit) limits bytes).mapError .snapshot)
  have original : Snapshot.check (Failure := Unit) limits bytes = .ok snapshot := by
    cases source : Snapshot.check (Failure := Unit) limits bytes <;>
      simp [source, Except.mapError] at opened ⊢
    exact opened
  let schema ← compile limits snapshot
  return ⟨snapshot, schema, original⟩


@[expose] public section

def SupportedEncodings (metadata : Footer.ColumnMetadata) : Prop :=
  0 ∈ metadata.encodings ∧ metadata.encodings.all (fun code => code == 0 || code == 3) = true

instance (metadata : Footer.ColumnMetadata) : Decidable (SupportedEncodings metadata) := by
  unfold SupportedEncodings
  infer_instance

inductive ChunkCause where
  | missing
  | association
  | codec (original : Int)
  | encodings (original : List Int)
  | pageOffsets
  | rowCount (expected actual : Int)
  | span
  deriving DecidableEq, Repr

inductive ChunkError where
  | groupOrdinal (original : Nat)
  | columnOrdinal (original : Nat)
  | column (group ordinal : Nat) (path : List String) (original : ChunkCause)
  deriving DecidableEq, Repr

structure ChunkBinding {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) (group column : Nat) where
  leaf : Leaf
  rowGroup : Footer.RowGroup
  chunk : Footer.ColumnChunk
  span : Footer.Span
  leafAt : schema.leaves[column]? = some leaf
  groupAt : snapshot.groupAt group = some rowGroup
  chunkAt : rowGroup.columns[column]? = some chunk
  path : chunk.metadata.pathInSchema = leaf.site.location.path
  physical : chunk.metadata.physicalType = leaf.kind.physical
  codec : chunk.metadata.codec = 0
  encodings : SupportedEncodings chunk.metadata
  pageOffsets : chunk.metadata.dictionaryPageOffset = none ∧ chunk.metadata.indexPageOffset = none
  rowCount : chunk.metadata.numValues = rowGroup.numRows
  originalSpan : Page.columnSpan snapshot.footer.start chunk.metadata = some span

end

private def checked {ε : Type} (p : Prop) [Decidable p] (error : ε) : Except ε (PLift p) :=
  if yes : p then .ok ⟨yes⟩ else .error error

private def lookup {α ε : Type} (source : Option α) (error : ε) :
    Except ε {value // source = some value} :=
  match source with
  | some result => .ok ⟨result, rfl⟩
  | none => .error error

/-- Bind the exact selected column in one original row group. Admission
here concerns footer metadata only. The next reader must still validate
the actual page kind, encodings, boundaries and body. -/
public def bindChunk {limits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled limits snapshot) (group column : Nat) :
    Except ChunkError (ChunkBinding schema group column) := do
  let ⟨rowGroup, originalGroup⟩ ← lookup (snapshot.groupAt group) (.groupOrdinal group)
  let ⟨leaf, originalLeaf⟩ ← lookup schema.leaves[column]? (.columnOrdinal column)
  let fail := ChunkError.column group column leaf.site.location.path
  let ⟨chunk, originalChunk⟩ ← lookup rowGroup.columns[column]? (fail .missing)
  let metadata := chunk.metadata
  let ⟨⟨path, physical⟩⟩ ← checked
    (metadata.pathInSchema = leaf.site.location.path ∧ metadata.physicalType = leaf.kind.physical)
    (fail .association)
  let ⟨codec⟩ ← checked (metadata.codec = 0) (fail (.codec metadata.codec))
  let ⟨encodings⟩ ← checked (SupportedEncodings metadata) (fail (.encodings metadata.encodings))
  let ⟨offsets⟩ ← checked (metadata.dictionaryPageOffset = none ∧ metadata.indexPageOffset = none) (fail .pageOffsets)
  let ⟨rowCount⟩ ← checked (metadata.numValues = rowGroup.numRows) (fail (.rowCount rowGroup.numRows metadata.numValues))
  let ⟨span, originalSpan⟩ ← lookup (Page.columnSpan snapshot.footer.start metadata) (fail .span)
  return ⟨leaf, rowGroup, chunk, span, originalLeaf, originalGroup, originalChunk, path,
    physical, codec, encodings, offsets, rowCount, originalSpan⟩

end Silmaril.Formats.Parquet.RecursiveSchema
