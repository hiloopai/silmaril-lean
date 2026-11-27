module

public import Silmaril.Formats.Arrow.BinaryView.Stream.Defs
public import Silmaril.Formats.Parquet.FlatInt32Writer.Compact.Defs
public import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Defs

/-! One annotated, uncompressed PLAIN BYTE_ARRAY V1 group per Utf8View batch. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc

open FlatInt32Writer
open Arrow.BinaryView

structure Limits where
  file : File.Limits := {}
  maxGroups : Nat := 4096

def Limits.page (limits : Limits) : PlainByteArrayV1Writer.Limits :=
  let framing := limits.file.column.framing
  ⟨⟨framing.header, framing.maxHeaderBytes, limits.file.scalar⟩, limits.file.values⟩

structure Source where
  name : String
  nullable : Bool
  batches : List (List (Option String))

def Source.observed (source : Source) : Stream.Observed :=
  ⟨⟨source.name, source.nullable, .utf8⟩, source.batches⟩

def Source.layout (source : Source) : FlatColumn.Layout :=
  if source.nullable then .optional else .required

def Source.totalRows (source : Source) : Nat := (source.batches.map List.length).sum

inductive Error where
  | source (cause : Stream.Error)
  | expectedUtf8View
  | groupLimit (maximum actual : Nat)
  | rowLimit (maximum actual : Nat)
  | schemaLimit
  | nullInRequired (group : Nat)
  | page (group : Nat) (cause : PlainByteArrayV1Writer.Error)
  | chunkLimit (group maximum actual : Nat)
  | fileLimit
  | footer (cause : Compact.Error)
  | extent
  | openReadback (cause : Utf8.Error)
  | groupReadback (group : Nat) (cause : Utf8.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

/-- The explicit one-field UTF-8 view reader consumes the original stream through EOS. -/
def readSource (ipc : Arrow.Limits) (view : Column.Limits) (input : KBytes) : Except Error Source := do
  match ← (Stream.read ipc view input).mapError .source with
  | ⟨⟨name, nullable, .utf8⟩, batches⟩ => return ⟨name, nullable, batches⟩
  | ⟨⟨_, _, .binary⟩, _⟩ => throw .expectedUtf8View

/-- Emit physical BYTE_ARRAY with ConvertedType.UTF8 (0) and LogicalType.STRING (1). -/
def stringLeaf (column : Compact.ColumnIndex) : Compact.Write Unit := do
  Compact.field 1 5
  Compact.integer .i32 6
  Compact.field 2 5
  Compact.integer .i32 (if column.optional then 1 else 0)
  Compact.field 1 8
  Compact.text column.name
  Compact.field 2 5
  Compact.integer .i32 0
  Compact.field 4 12
  Compact.field 1 12
  Compact.octet 0
  Compact.octet 0
  Compact.octet 0

namespace Internal

def fileLimit (limits : Limits) : Nat := min limits.file.maxFileBytes (2^63 - 1)

def checkBudget (limits : Limits) (source : Source) : Except Error Unit := do
  let compact := limits.file.snapshot.footer.compact
  let groups := min limits.maxGroups compact.maxCollectionSize
  if source.batches.length > groups then throw (.groupLimit groups source.batches.length)
  let rows := min limits.file.maxFileRows (2^63 - 1)
  if source.totalRows > rows then throw (.rowLimit rows source.totalRows)
  if compact.maxCollectionSize < 2 || source.name.utf8ByteSize > compact.maxBinaryBytes then throw .schemaLimit

def textBytes (text : String) : Bytes := ⟨text.toByteArray⟩

def pageInput (nullable : Bool) (index : Nat) (slots : List (Option String)) :
    Except Error PlainByteArrayV1Writer.Input :=
  if nullable then .ok (.optional (slots.map (Option.map textBytes)))
  else
    match slots.mapM id with
    | none => .error (.nullInRequired index)
    | some values => .ok (.required (values.map textBytes))

def measure (limits : PlainByteArrayV1Writer.Limits) (input : PlainByteArrayV1Writer.Input) :
    Except PlainByteArrayV1Writer.Error Nat := do
  if ¬ input.Fits limits then throw .bodyBudget
  let some header := PlainV1Writer.encodeHeader input.numValues input.bodySize | throw .headerInteger
  if limits.page.headerBytes < header.length then throw .headerBudget
  return header.length + input.bodySize

structure Group where
  input : PlainByteArrayV1Writer.Input
  span : Footer.Span

/-- Each measured page has a span even when its row count is zero. -/
def place (limits : Limits) (nullable : Bool) :
    Nat → Nat → List (List (Option String)) → Except Error (List Group)
  | _, _, [] => .ok []
  | start, index, slots :: rest => do
    let input ← pageInput nullable index slots
    let size ← (measure limits.page input).mapError (.page index)
    if size > limits.file.column.maxChunkBytes then
      throw (.chunkLimit index limits.file.column.maxChunkBytes size)
    if start + size + 8 > fileLimit limits then throw .fileLimit
    let stop := start + size
    let tail ← place limits nullable stop (index + 1) rest
    return ⟨input, ⟨start, stop⟩⟩ :: tail

/-- Measure the data and budget the footer before emitting page bodies. -/
def assemble (limits : Limits) (source : Source) : Except Error Bytes := do
  checkBudget limits source
  let groups ← place limits source.nullable 4 0 source.batches
  let dataStop := (groups.getLast?.map (·.span.stop)).getD 4
  if dataStop + 8 > fileLimit limits then throw .fileLimit
  let cap := min (min limits.file.snapshot.footer.maxFooterBytes (2^32 - 1)) (fileLimit limits - dataStop - 8)
  let column := fun span => (⟨source.name, source.nullable, span⟩ : Compact.ColumnIndex)
  let indexed := groups.map fun group => (group.input.numValues, [column group.span])
  let footer ← (Compact.encodeGroupsFor 6 stringLeaf cap [column ⟨0, 0⟩] indexed).mapError .footer
  let pages ← groups.zipIdx.mapM fun (group, index) => do
    let page ← (PlainByteArrayV1Writer.emit limits.page group.input).mapError (.page index)
    if page.wire.length ≠ group.span.stop - group.span.start then throw .extent
    return page
  let payload := Bytes.ofList (pages.flatMap (·.wire.toList))
  let prefixBytes := (Footer.magic.append payload).append footer
  return (prefixBytes.append (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic

def readGroups {name : String} {layout : FlatColumn.Layout} (limits : Limits) (checked : Utf8.Checked name layout) :
    Except Error (List (List (Option String))) :=
  (List.range checked.physical.snapshot.groupCount).mapM fun index =>
    (checked.readGroup limits.file index).mapError (.groupReadback index)

/-- Publish only a file whose annotation and every text group read back. -/
def certify (limits : Limits) (source : Source) (wire : Bytes) : Except Error Bytes := do
  let checked ← (Utf8.openFile limits.file wire source.name source.layout).mapError .openReadback
  let batches ← readGroups limits checked
  if checked.physical.snapshot.metadata.schema.length = 2 ∧
      checked.annotation = .logicalAndConverted ∧ batches = source.batches then .ok wire
  else .error .readbackMismatch

end Internal

def emit (limits : Limits) (source : Source) : Except Error Bytes := do
  let wire ← Internal.assemble limits source
  Internal.certify limits source wire

def convert (ipc : Arrow.Limits) (view : Column.Limits) (limits : Limits) (input : KBytes) :
    Except Error Bytes := do
  let source ← readSource ipc view input
  emit limits source

/-- The bounded output opens at the same descriptor and reads every original
IPC batch as one framed PLAIN group with exact nullable UTF-8 octets. -/
def SinkWire (limits : Limits) (source : Source) (wire : Bytes) : Prop :=
  ∃ checked : Utf8.Checked source.name source.layout,
    wire.length ≤ limits.file.maxFileBytes ∧
    Utf8.openFile limits.file wire source.name source.layout = .ok checked ∧
    checked.physical.snapshot.metadata.schema.length = 2 ∧
    checked.annotation = .logicalAndConverted ∧
    checked.physical.snapshot.groupCount = source.batches.length ∧
    List.Forall₂ (fun index slots =>
      checked.readGroup limits.file index = .ok slots ∧
      ∃ group, File.GroupWire checked.physical limits.file index group
        (slots.map (Option.map Internal.textBytes)))
      (List.range checked.physical.snapshot.groupCount) source.batches

end Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc
