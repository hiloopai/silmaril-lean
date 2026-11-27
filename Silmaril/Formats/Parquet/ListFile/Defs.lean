module

public import Silmaril.Formats.Parquet.Footer.NestedLeaf.Defs
public import Silmaril.Formats.Parquet.ListPage.Defs
public import Silmaril.Formats.Parquet.Page.Defs

/-! One canonical nullable INT32 LIST column from an immutable Parquet file.
Each group has one complete uncompressed PLAIN V1 data page. -/

public section

namespace Silmaril.Formats.Parquet.ListFile

open Silmaril.Formats.Parquet.Footer
open ThriftCompact
open Traversal (Field Reader)
open Silmaril.Relational

structure Limits where
  maxFileBytes : Nat := 64 * 1024 * 1024
  snapshot : Snapshot.Limits := {}
  framing : Page.Limits := {}
  page : ListPage.Limits := {}

inductive OpenError where
  | fileLimit
  | snapshot (cause : Snapshot.Error Unit)
  | shape
  | schemaItems (cause : NestedLeaf.Error)
  | schemaExtent
  | compact (cause : ColumnOrder.Error)
  | missingList
  | invalidList
  | otherAnnotation
  deriving DecidableEq, Repr

structure Shape where
  root : Footer.SchemaElement
  outer : Footer.SchemaElement
  repeated : Footer.SchemaElement
  element : Footer.SchemaElement

def Shape.path (shape : Shape) : List String :=
  [shape.outer.name, shape.repeated.name, shape.element.name]

def Shape.admitted (shape : Shape) : Bool :=
  shape.root.numChildren == some 1 &&
  shape.outer.physicalType.isNone && shape.outer.repetition == some .optional &&
  shape.outer.numChildren == some 1 &&
  shape.repeated.physicalType.isNone && shape.repeated.repetition == some .repeated &&
  shape.repeated.name == "list" && shape.repeated.numChildren == some 1 &&
  shape.element.physicalType == some .int32 && shape.element.typeLength.isNone &&
  shape.element.repetition == some .optional &&
  shape.element.name == "element" && shape.element.numChildren.getD 0 == 0

def readShape (schema : List Footer.SchemaElement) : Except OpenError Shape :=
  match schema with
  | [root, outer, repeated, element] =>
    let shape : Shape := ⟨root, outer, repeated, element⟩
    if shape.admitted then .ok shape else .error .shape
  | _ => .error .shape

def unannotated (item : ColumnOrder.Item) : Bool :=
  !(item.fields.any fun field => field.id == 6 || field.id == 10)

/-- If supplied alongside the modern tag, ConvertedType must also be LIST. -/
def checkConvertedList (reader : Traversal.Reader) (legacy : Option Field) : Except OpenError Unit := do
  if let some field := legacy then
    if field.type ≠ .payload .i32 then return ← throw .invalidList
    let (value, stop) ← (readSigned .i32 reader.mode reader.source field.start).mapError
      (.compact ∘ .compact ∘ .compact)
    if ¬ (value = 3 ∧ stop = field.stop) then return ← throw .invalidList

/-- SchemaElement field 10 selects the sole LogicalType arm, LIST (field 3).
ListType is an empty struct in the pinned IDL. -/
def checkList (reader : Reader) (outer : ColumnOrder.Item) : Except OpenError Unit := do
  let some logical ← (ColumnOrder.field? outer.fields 10).mapError .compact | throw .missingList
  if logical.type ≠ .payload .struct then return ← throw .invalidList
  let (members, stop) ← (Traversal.readStruct reader logical.start).mapError (.compact ∘ .compact)
  let [member] := members | throw .invalidList
  if ¬ (stop = logical.stop ∧ member.id = 3 ∧ member.type = .payload .struct) then
    return ← throw .invalidList
  let (payload, next) ← (Traversal.readStruct reader member.start).mapError (.compact ∘ .compact)
  if ¬ (payload = [] ∧ next = member.stop) then return ← throw .invalidList
  let legacy ← (ColumnOrder.field? outer.fields 6).mapError .compact
  checkConvertedList reader legacy

def ConvertedWire (reader : Traversal.Reader) : Option Field → Prop
  | none => True
  | some field => field.type = .payload .i32 ∧
    readSigned .i32 reader.mode reader.source field.start = .ok (3, field.stop)

structure AnnotationWire (reader : Traversal.Reader) (outer : ColumnOrder.Item) : Prop where
  fields : ∃ logical member legacy,
    outer.fields.filter (·.id == 10) = [logical] ∧ logical.type = .payload .struct ∧
    Traversal.readStruct reader logical.start = .ok ([member], logical.stop) ∧
    member.id = 3 ∧ member.type = .payload .struct ∧
    Traversal.readStruct reader member.start = .ok ([], member.stop) ∧
    ColumnOrder.field? outer.fields 6 = .ok legacy ∧ ConvertedWire reader legacy

structure Checked where
  private mk ::
  snapshot : Snapshot.Checked
  shape : Shape
  limits : Limits

def openFile (limits : Limits) (source : Bytes) : Except OpenError Checked := do
  if limits.maxFileBytes < source.length then return ← throw .fileLimit
  let snapshot ← (Snapshot.check (Failure := Unit) limits.snapshot source).mapError .snapshot
  let shape ← readShape snapshot.metadata.schema
  let (container, items) ← (NestedLeaf.readItems limits.snapshot.footer snapshot).mapError .schemaItems
  let [root, outer, repeated, element] := items | throw .schemaExtent
  let reader := ColumnOrder.footerReader limits.snapshot.footer snapshot
  if ¬ (ColumnOrder.Slot.within reader ⟨container, outer⟩ ∧
        ColumnOrder.Slot.within reader ⟨container, element⟩) then return ← throw .schemaExtent
  if !(unannotated root && unannotated repeated && unannotated element) then
    return ← throw .otherAnnotation
  checkList reader outer
  pure ⟨snapshot, shape, limits⟩

/-- The four items retain the original schema ordinals. In this one-leaf
schema the element at ordinal 3 is physical column 0. -/
structure OpenWire (limits : Limits) (source : Bytes) (checked : Checked) : Prop where
  cap : source.length ≤ limits.maxFileBytes
  limitsEq : checked.limits = limits
  snapshot : Snapshot.check (Failure := Unit) limits.snapshot source = .ok checked.snapshot
  shape : checked.snapshot.metadata.schema =
    [checked.shape.root, checked.shape.outer, checked.shape.repeated, checked.shape.element] ∧
    checked.shape.admitted = true
  wire : ∃ container root outer repeated element,
    let reader := ColumnOrder.footerReader limits.snapshot.footer checked.snapshot
    NestedLeaf.ItemsWire limits.snapshot.footer checked.snapshot container [root, outer, repeated, element] ∧
    ColumnOrder.Slot.within reader ⟨container, outer⟩ ∧
    ColumnOrder.Slot.within reader ⟨container, element⟩ ∧
    unannotated root = true ∧ unannotated repeated = true ∧ unannotated element = true ∧
    AnnotationWire reader outer

inductive ReadError where
  | groupOrdinal (index : Nat)
  | column
  | codec (actual : Int)
  | unsupportedOffsets
  | chunkBounds
  | framing (cause : Page.Error)
  | pageCount
  | pageKind
  | slotCount (footer : Int) (page : Nat)
  | bodyLimit
  | payloadBounds
  | page (cause : ListPage.Error)
  deriving DecidableEq, Repr

/-- The selected local chunk and its original checked frames. -/
structure FramedGroup where
  group : Footer.RowGroup
  chunk : Footer.ColumnChunk
  span : Footer.Span
  frames : List Page.Frame

/-- Select the original group and physical column ordinal 0 of the admitted
LIST schema, then frame the entire declared chunk on the same snapshot. -/
def Checked.frameGroupWith (checked : Checked) (codec : Int) (allowDictionary : Bool) (index : Nat) : Except ReadError FramedGroup := do
  let some group := checked.snapshot.groupAt index | throw (.groupOrdinal index)
  let [chunk] := group.columns | throw .column
  let metadata := chunk.metadata
  if ¬ (metadata.pathInSchema = checked.shape.path ∧ metadata.physicalType = .int32) then
    return ← throw .column
  if metadata.codec ≠ codec then return ← throw (.codec metadata.codec)
  if (!allowDictionary && metadata.dictionaryPageOffset.isSome) || metadata.indexPageOffset.isSome then
    return ← throw .unsupportedOffsets
  let some span := Page.columnSpan checked.snapshot.footer.start metadata | throw .chunkBounds
  let frames ← (Page.readChunk checked.limits.framing checked.snapshot.bytes span).mapError .framing
  pure ⟨group, chunk, span, frames⟩

/-- The original non-dictionary profiles. -/
def Checked.frameGroupFor (checked : Checked) (codec : Int) (index : Nat) : Except ReadError FramedGroup :=
  checked.frameGroupWith codec false index

/-- The original uncompressed profile. -/
def Checked.frameGroup (checked : Checked) (index : Nat) : Except ReadError FramedGroup :=
  checked.frameGroupFor 0 index

/-- The group is the row boundary. One complete frame must fill the chunk.
The page's slot count includes structural markers and can exceed its row count. -/
def Checked.readGroup (checked : Checked) (index : Nat) : Except ReadError (List ListPage.Row) := do
  let framed ← checked.frameGroup index
  let [frame] := framed.frames | throw .pageCount
  let group := framed.group
  let metadata := framed.chunk.metadata
  let .dataV1 info := frame.value.kind | throw .pageKind
  if metadata.numValues ≠ (info.numValues : Int) then
    return ← throw (.slotCount metadata.numValues info.numValues)
  if checked.limits.page.maxBodyBytes < frame.value.compressedSize then return ← throw .bodyLimit
  let some body := checked.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) |
    throw .payloadBounds
  (ListPage.decodeV1 checked.limits.page metadata.codec frame.value group.numRows.toNat body).mapError .page

/-- Origin of the original selected chunk before a dictionary profile checks its offsets. -/
structure ChunkFrameWire (checked : Checked) (index : Nat) (framed : FramedGroup)
    (codecId : Int) : Prop where
  group : checked.snapshot.groupAt index = some framed.group
  chunk : framed.group.columns = [framed.chunk]
  path : framed.chunk.metadata.pathInSchema = checked.shape.path
  physical : framed.chunk.metadata.physicalType = .int32
  codec : framed.chunk.metadata.codec = codecId
  indexPageOffset : framed.chunk.metadata.indexPageOffset = none
  span : Page.columnSpan checked.snapshot.footer.start framed.chunk.metadata = some framed.span
  frames : Page.readChunk checked.limits.framing checked.snapshot.bytes framed.span = .ok framed.frames
  chain : Page.Chain framed.span framed.span.start framed.span.stop framed.frames

structure FramedGroupWire (checked : Checked) (index : Nat) (framed : FramedGroup)
    (codecId : Int := 0) : Prop where
  group : checked.snapshot.groupAt index = some framed.group
  chunk : framed.group.columns = [framed.chunk]
  path : framed.chunk.metadata.pathInSchema = checked.shape.path
  physical : framed.chunk.metadata.physicalType = .int32
  codec : framed.chunk.metadata.codec = codecId
  dictionaryOffset : framed.chunk.metadata.dictionaryPageOffset = none
  indexPageOffset : framed.chunk.metadata.indexPageOffset = none
  span : Page.columnSpan checked.snapshot.footer.start framed.chunk.metadata = some framed.span
  frames : Page.readChunk checked.limits.framing checked.snapshot.bytes framed.span = .ok framed.frames
  chain : Page.Chain framed.span framed.span.start framed.span.stop framed.frames

/-- Original zero-based group, physical column 0, and complete frame from the
same checked source, with separate footer row and level-slot counts. -/
structure GroupWire (checked : Checked) (index : Nat) (slots : List ListPage.Row) : Prop where
  wire : ∃ group chunk span frame body info,
    checked.snapshot.groupAt index = some group ∧ group.columns = [chunk] ∧
    chunk.metadata.pathInSchema = checked.shape.path ∧ chunk.metadata.physicalType = .int32 ∧
    chunk.metadata.codec = 0 ∧
    chunk.metadata.dictionaryPageOffset = none ∧ chunk.metadata.indexPageOffset = none ∧
    Page.columnSpan checked.snapshot.footer.start chunk.metadata = some span ∧
    Page.readChunk checked.limits.framing checked.snapshot.bytes span = .ok [frame] ∧
    Page.Chain span span.start span.stop [frame] ∧
    checked.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some body ∧
    frame.value.kind = .dataV1 info ∧ chunk.metadata.numValues = (info.numValues : Int) ∧
    ListPage.PageWire checked.limits.page chunk.metadata.codec frame.value group.numRows.toNat body slots ∧
    ListPage.Wire checked.limits.page group.numRows.toNat info.numValues body slots ∧
    slots.length = group.numRows.toNat

inductive Error where
  | openFailure (cause : OpenError)
  | groupFailure (index : Nat) (cause : ReadError)
  deriving DecidableEq, Repr

/-- Arrow event schema for one nullable LIST of nullable INT32 elements. -/
inductive Kind where
  | nullableListOfNullableInt32
  deriving DecidableEq, Repr

abbrev Cell (_ : Kind) := List (Option Int32)

def schema (checked : Checked) : Scan.Schema String Kind :=
  ⟨1, fun _ => (checked.shape.outer.name, .nullableListOfNullableInt32)⟩

def rows (checked : Checked) (slots : List ListPage.Row) : Parquet.Reader.RowGroup (schema checked) Cell :=
  slots.map fun slot _ => slot

def rowsAt (checked : Checked) (index : Nat) :
    Except Error (Parquet.Reader.RowGroup (schema checked) Cell) :=
  ((checked.readGroup index).mapError (.groupFailure index)).map (rows checked)

def groupSource (checked : Checked) : Parquet.Reader.Source Nat (schema checked) Cell Error :=
  ⟨List.range checked.snapshot.groupCount, rowsAt checked, fun _ => .ok ()⟩

def openSource (limits : Limits) (source : Bytes) : Parquet.Reader.OpenResult Nat String Cell Error :=
  ((openFile limits source).mapError .openFailure).map fun checked => ⟨schema checked, groupSource checked⟩

def readAll (limits : Limits) (source : Bytes) : Arrow.Events.EventStream String Cell Error :=
  Parquet.Reader.readAll (openSource limits source)

end Silmaril.Formats.Parquet.ListFile
