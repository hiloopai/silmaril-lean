module

public import Silmaril.Formats.Parquet.Footer.Defs

/-! Bounded Compact serialization for flat INT32 footers. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatInt32Writer.Compact

structure ColumnIndex where
  name : String
  optional : Bool
  span : Footer.Span
  deriving DecidableEq, Repr

def ColumnIndex.size (column : ColumnIndex) : Nat := column.span.stop - column.span.start

def ColumnIndex.schema (column : ColumnIndex) : Footer.SchemaElement :=
  ⟨some .int32, none, some (if column.optional then .optional else .required), column.name, none⟩

def ColumnIndex.metadata (column : ColumnIndex) (rows : Nat) : Footer.ColumnChunk :=
  ⟨0, ⟨.int32, [0, 3], [column.name], 0, rows, column.size, column.size,
    column.span.start, none, none, none, none⟩, none, none, none, none⟩

def schemaRoot (width : Nat) : Footer.SchemaElement := ⟨none, none, none, "schema", some width⟩

def metadata (rows : Nat) (columns : List ColumnIndex) : Footer.Metadata :=
  ⟨1, schemaRoot columns.length :: columns.map ColumnIndex.schema, rows,
    [⟨columns.map (fun column => column.metadata rows), (columns.map ColumnIndex.size).sum,
      rows, none, none⟩], none⟩

inductive Error where
  | byteLimit
  | integerRange
  deriving DecidableEq, Repr

structure Buffer where
  remaining : Nat
  bytes : Bytes

abbrev Write := StateT Buffer (Except Error)

def put (bytes : Bytes) : Write Unit := do
  let buffer ← get
  if buffer.remaining < bytes.length then throw .byteLimit
  set (⟨buffer.remaining - bytes.length, buffer.bytes.append bytes⟩ : Buffer)

def octet (value : Nat) : Write Unit := put (Bytes.ofList [UInt8.ofNat value])

def field (delta tag : Nat) : Write Unit := octet (16 * delta + tag)

def integer (width : ThriftCompact.Width) (value : Int) : Write Unit := do
  let some bytes := ThriftCompact.encodeSigned? width value | throw .integerRange
  put bytes

def length (size : Nat) : Write Unit := do
  if 2 ^ 31 ≤ size then throw .integerRange
  put (Bytes.ofList (ThriftCompact.varintBytes size))

def text (value : String) : Write Unit := do
  length value.utf8ByteSize
  if (← get).remaining < value.utf8ByteSize then throw .byteLimit
  put ⟨value.toUTF8⟩

def listHeader (tag size : Nat) : Write Unit :=
  if size < 15 then octet (16 * size + tag) else do
    octet (0xf0 + tag)
    length size

def root (width : Nat) : Write Unit := do
  field 4 8
  text "schema"
  field 1 5
  integer .i32 width
  octet 0

inductive LeafAnnotation where
  | unannotated
  | date

def leafAnnotated (annotation : LeafAnnotation) (column : ColumnIndex) : Write Unit := do
  field 1 5
  integer .i32 1
  field 2 5
  integer .i32 (if column.optional then 1 else 0)
  field 1 8
  text column.name
  match annotation with
  | .unannotated => pure ()
  | .date =>
    -- From SchemaElement.name (4) to ConvertedType.DATE (6).
    field 2 5
    integer .i32 6
    -- LogicalType (10) contains only DATE (6) with an empty DateType struct.
    field 4 12
    field 6 12
    octet 0
    octet 0
  octet 0

def leaf (column : ColumnIndex) : Write Unit := leafAnnotated .unannotated column

/-- The flat PLAIN chunk shape is common to the fixed-width physical writers. -/
def chunkFor (physical : Int) (rows : Nat) (column : ColumnIndex) : Write Unit := do
  field 2 6
  integer .i64 0
  field 1 12
  field 1 5
  integer .i32 physical
  field 1 9
  listHeader 5 2
  integer .i32 0
  integer .i32 3
  field 1 9
  listHeader 8 1
  text column.name
  field 1 5
  integer .i32 0
  field 1 6
  integer .i64 rows
  field 1 6
  integer .i64 column.size
  field 1 6
  integer .i64 column.size
  field 2 6
  integer .i64 column.span.start
  octet 0
  octet 0

def chunk (rows : Nat) (column : ColumnIndex) : Write Unit := chunkFor 1 rows column

structure TypedColumnIndex where
  physical : Int
  column : ColumnIndex

/-- Serialize one flat row group with a physical type at each chunk position. -/
def groupTyped (rows : Nat) (columns : List TypedColumnIndex) : Write Unit := do
  field 1 9
  listHeader 12 columns.length
  for column in columns do chunkFor column.physical rows column.column
  field 1 6
  let size : Nat := (columns.map (·.column.size)).sum
  integer .i64 size
  field 1 6
  integer .i64 rows
  octet 0

def groupFor (physical : Int) (rows : Nat) (columns : List ColumnIndex) : Write Unit :=
  groupTyped rows (columns.map fun column => ⟨physical, column⟩)

def group (rows : Nat) (columns : List ColumnIndex) : Write Unit := groupFor 1 rows columns

def Internal.footerGroupsTyped (leaves : List (Write Unit))
    (groups : List (Nat × List TypedColumnIndex)) : Write Unit := do
  field 1 5
  integer .i32 1
  field 1 9
  listHeader 12 (leaves.length + 1)
  root leaves.length
  for writeLeaf in leaves do writeLeaf
  field 1 6
  integer .i64 (groups.map Prod.fst).sum
  field 1 9
  listHeader 12 groups.length
  for (rows, chunks) in groups do groupTyped rows chunks
  octet 0

def Internal.tagGroups (physical : Int) (groups : List (Nat × List ColumnIndex)) :
    List (Nat × List TypedColumnIndex) :=
  groups.map fun (rows, chunks) => (rows, chunks.map fun column => ⟨physical, column⟩)

def Internal.footerGroupsWriting (physical : Int) (leaves : List (Write Unit))
    (groups : List (Nat × List ColumnIndex)) : Write Unit :=
  Internal.footerGroupsTyped leaves (Internal.tagGroups physical groups)

/-- The same Compact byte cap covers each ordered schema leaf and all typed chunks. -/
def encodeGroupsTyped (limit : Nat) (leaves : List (Write Unit))
    (groups : List (Nat × List TypedColumnIndex)) : Except Error Bytes :=
  ((Internal.footerGroupsTyped leaves groups).run ⟨limit, .empty⟩).map (·.2.bytes)

def Internal.footerGroupsFor (physical : Int) (writeLeaf : ColumnIndex → Write Unit) (columns : List ColumnIndex)
    (groups : List (Nat × List ColumnIndex)) : Write Unit :=
  Internal.footerGroupsWriting physical (columns.map writeLeaf) groups

/-- Encode individual ordered leaf annotations with a common physical chunk type. -/
def encodeGroupsWriting (physical : Int) (limit : Nat) (leaves : List (Write Unit))
    (groups : List (Nat × List ColumnIndex)) : Except Error Bytes :=
  ((Internal.footerGroupsWriting physical leaves groups).run ⟨limit, .empty⟩).map (·.2.bytes)

def Internal.footerGroups (annotation : LeafAnnotation) (columns : List ColumnIndex)
    (groups : List (Nat × List ColumnIndex)) : Write Unit :=
  Internal.footerGroupsFor 1 (leafAnnotated annotation) columns groups

/-- Encode a flat footer using the supplied leaf serializer and matching
physical type code for every PLAIN chunk. -/
def encodeGroupsFor (physical : Int) (writeLeaf : ColumnIndex → Write Unit) (limit : Nat)
    (columns : List ColumnIndex) (groups : List (Nat × List ColumnIndex)) : Except Error Bytes :=
  encodeGroupsWriting physical limit (columns.map writeLeaf) groups

/-- Encode one shared schema and the ordered list of row counts and chunk indices. -/
def encodeGroups (annotation : LeafAnnotation) (limit : Nat) (columns : List ColumnIndex)
    (groups : List (Nat × List ColumnIndex)) : Except Error Bytes :=
  encodeGroupsFor 1 (leafAnnotated annotation) limit columns groups

def footerAnnotated (annotation : LeafAnnotation) (rows : Nat) (columns : List ColumnIndex) :
    Write Unit :=
  Internal.footerGroups annotation columns [(rows, columns)]

def footer (rows : Nat) (columns : List ColumnIndex) : Write Unit :=
  footerAnnotated .unannotated rows columns

/-- Each write consumes part of the caller's exact Compact byte budget. -/
def encodeAnnotated (annotation : LeafAnnotation) (limit rows : Nat) (columns : List ColumnIndex) :
    Except Error Bytes :=
  encodeGroups annotation limit columns [(rows, columns)]

def encode (limit rows : Nat) (columns : List ColumnIndex) : Except Error Bytes :=
  encodeAnnotated .unannotated limit rows columns

end Silmaril.Formats.Parquet.FlatInt32Writer.Compact
