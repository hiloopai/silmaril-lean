module

public import Silmaril.Formats.Parquet.Page.Checksum.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Defs

/-! Opt-in Snappy PLAIN dictionaries with checked STRING RLE_DICTIONARY data pages. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy

structure Limits extends Dictionary.Limits where
  maxExpandedPageBytes : Nat := 16 * 1024 * 1024
  maxExpandedChunkBytes : Nat := 64 * 1024 * 1024

abbrev Checked (name : String) := Dictionary.Checked name

inductive DecodeError where
  | unadvertisedEncoding (actual : Int)
  | dictionaryEntryLimit (maximum actual : Nat)
  | checksum (cause : Page.Checksum.Error)
  | payload (cause : Payload.Error)
  | entries (cause : Plain.Error)
  | text (cause : Dictionary.DecodeError)
  | missingDictionary
  | indices (cause : DictionaryIndex.Error)
  deriving DecidableEq, Repr

abbrev GroupError := FlatColumn.Error DecodeError

inductive Error where
  | openFile (cause : Utf8.Error)
  | column (cause : GroupError)
  | writer (cause : Arrow.MixedFlat.OrderedWriter.Error)
  deriving DecidableEq, Repr

def Limits.expandedDictionaryBytes (limits : Limits) : Nat :=
  min limits.maxDictionaryBytes limits.maxExpandedPageBytes

def Limits.dictionaryBounds (limits : Limits) (frame : Page.Frame) : Payload.Bounds :=
  ⟨frame.value.compressedSize, min limits.maxDictionaryBytes limits.file.column.maxPageBytes,
    frame.value.uncompressedSize, limits.expandedDictionaryBytes, 0⟩

def Limits.entryBytes (limits : Limits) : Plain.ByteArray.Limits :=
  ⟨limits.expandedDictionaryBytes, limits.file.maxValueBytes⟩

def Limits.scalar (limits : Limits) : ScalarPage.Limits :=
  ⟨limits.file.column.maxPageBytes, limits.maxExpandedPageBytes,
    ⟨limits.file.column.maxRows, limits.maxExpandedPageBytes⟩, 0⟩

def Limits.indices (limits : Limits) : Hybrid.Limits :=
  ⟨limits.file.column.maxRows, limits.maxExpandedPageBytes⟩

def storedBytes (frames : List Page.Frame) : Nat :=
  (frames.map fun frame => frame.header.stop - frame.header.start + frame.value.compressedSize).sum

/-- Every on-disk header contributes once to the expanded chunk size. -/
def expandedBytes (frames : List Page.Frame) : Nat :=
  (frames.map fun frame => frame.header.stop - frame.header.start + frame.value.uncompressedSize).sum

/-- Check the original stored CRC and expansion bound before decoding the
exact PLAIN entries as opaque bytes. -/
def readDictionaryBytesWith (codec : Payload.Codec) (gzipCalls : Nat) (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (frame : Page.Frame) : Except (FlatColumn.PageError DecodeError) (List Bytes) := do
  let .dictionary header := frame.value.kind | throw .unsupportedKind
  if header.encoding ≠ 0 then .error (.encoding header.encoding)
  else if !metadata.encodings.contains 0 then .error (.decode (.unadvertisedEncoding 0))
  else if limits.maxDictionaryEntries < header.numValues then
    .error (.decode (.dictionaryEntryLimit limits.maxDictionaryEntries header.numValues))
  else
    let bounds := { limits.dictionaryBounds frame with gzipCallLimit := gzipCalls }
    if bounds.outputLimit < bounds.expectedSize then .error (.decode (.payload .outputLimit))
    else do
      let _ ← (Page.Checksum.verify bounds.compressedLimit source frame).mapError (.decode ∘ .checksum)
      let expanded ← (Payload.decode bounds codec.id
        (Page.Checksum.payloadBytes source frame).toList).mapError (.decode ∘ .payload)
      (Plain.ByteArray.decode limits.entryBytes header.numValues (Bytes.ofList expanded)).mapError (.decode ∘ .entries)

def readDictionaryBytes (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (frame : Page.Frame) : Except (FlatColumn.PageError DecodeError) (List Bytes) :=
  readDictionaryBytesWith .snappy 0 limits metadata source frame

/-- Interpret every checked dictionary entry as strict STRING, including unused entries. -/
def readDictionary (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (frame : Page.Frame) : Except (FlatColumn.PageError DecodeError) (Array String) := do
  let raw ← readDictionaryBytes limits metadata source frame
  let texts ← (raw.zipIdx.mapM Dictionary.decodeEntry).mapError (.decode ∘ .text)
  return texts.toArray

/-- Verify the entire stored body, including the original V2 level bytes.
The scalar adapter selects the codec for the index suffix from the original flag. -/
def decodeIndexPageWith {α : Type} (codec : Payload.Codec) (gzipCalls : Nat) (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (dictionary : Option (Array α)) (frame : Page.Frame) :
    Except (FlatColumn.PageError DecodeError) (List (Option α)) := do
  let some params := FlatColumn.pageParameters .optional codec.id frame.value |
    throw .unsupportedKind
  let cap := min limits.file.column.maxRows (Hybrid.runLimit - 1)
  if params.encoding ≠ 8 then .error (.encoding params.encoding)
  else if !metadata.encodings.contains 8 then .error (.decode (.unadvertisedEncoding 8))
  else if cap < params.numValues then .error (.slotLimit cap params.numValues)
  else do
    let some entries := dictionary | throw (.decode .missingDictionary)
    if limits.maxExpandedPageBytes < frame.value.uncompressedSize then .error (.decode (.payload .outputLimit))
    else do
      let _ ← (Page.Checksum.verify limits.file.column.maxPageBytes source frame).mapError (.decode ∘ .checksum)
      (DictionaryIndex.decode entries params { limits.scalar with gzipCalls } limits.indices
        (Page.Checksum.payloadBytes source frame)).mapError (.decode ∘ .indices)

def decodeIndexPage {α : Type} (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (dictionary : Option (Array α)) (frame : Page.Frame) :
    Except (FlatColumn.PageError DecodeError) (List (Option α)) :=
  decodeIndexPageWith .snappy 0 limits metadata source dictionary frame

def decodePage := decodeIndexPage (α := String)

/-- Check the expanded frame sum and the exact footer extent before the client
can read a dictionary or data body. -/
def checkExpandedChunk {ε : Type} (limits : Limits) (metadata : Footer.ColumnMetadata)
    (group column : Nat) (name : String) (frames : List Page.Frame) : Except (FlatColumn.Error ε) Unit :=
  let size := expandedBytes frames
  if limits.maxExpandedChunkBytes < size then .error (.column group column name .chunkLimit)
  else if (size : Int) ≠ metadata.totalUncompressedSize then .error (.column group column name .bounds)
  else .ok ()

def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except GroupError (List (Option String)) := do
  checkExpandedChunk limits metadata group column name frames
  ByteArrayFallback.readFramesWith (readDictionary limits metadata source)
    (decodePage limits metadata source) metadata group column name rows frames

def readGroup {name : String} (limits : Limits) (checked : Checked name) (index : Nat) :
    Except GroupError (List (Option String)) :=
  ByteArrayFallback.readBoundGroupWithCodec .snappy limits.maxExpandedChunkBytes .rleDictionary
    checked.physical.binding limits.toLimits (readFrames limits) index

/-- A verified CRC status concerns exactly the advertised stored bytes. -/
def StoredWire (cap : Nat) (source : Bytes) (frame : Page.Frame) : Prop :=
  (∃ status, Page.Checksum.verify cap source frame = .ok status) ∧
  source.slice? frame.payload.start (some frame.payload.stop) = some (Page.Checksum.payloadBytes source frame) ∧
  (Page.Checksum.payloadBytes source frame).length = frame.value.compressedSize ∧
  frame.value.compressedSize ≤ cap

/-- The original stored dictionary expands to the exact PLAIN entry bytes in order. -/
def DictionaryBytesWireWith (codec : Payload.Codec) (limits : Limits) (source : Bytes) (frame : Page.Frame) (entries : List Bytes) : Prop :=
  ∃ header expanded,
    frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧ header.numValues ≤ limits.maxDictionaryEntries ∧
    StoredWire (limits.dictionaryBounds frame).compressedLimit source frame ∧
    Payload.Decodes frame.value.uncompressedSize codec (Page.Checksum.payloadBytes source frame).toList expanded ∧
    expanded.length = frame.value.uncompressedSize ∧ expanded.length ≤ limits.expandedDictionaryBytes ∧
    expanded = Plain.ByteArray.wire entries ∧ entries.length = header.numValues

def DictionaryBytesWire := DictionaryBytesWireWith .snappy

/-- Exact tagged index windows and nullable slots for a dictionary of any value type. -/
def IndexPageWireWith {α : Type} (codec : Payload.Codec) (gzipCalls : Nat) (limits : Limits) (source : Bytes) (entries : Array α)
    (frame : Page.Frame) (slots : List (Option α)) : Prop :=
  let body := Page.Checksum.payloadBytes source frame
  ∃ (params : ScalarPage.Parameters) (layout : FlatPage.Layout) (page : ScalarPage.Prepared) (indices : List Nat),
    FlatColumn.pageParameters .optional codec.id frame.value = some params ∧ params.encoding = 8 ∧
    StoredWire limits.file.column.maxPageBytes source frame ∧
    frame.value.uncompressedSize ≤ limits.maxExpandedPageBytes ∧
    ScalarPage.validateFor 8 params { limits.scalar with gzipCalls } body = .ok layout ∧
    ScalarPage.PreparedWire params { limits.scalar with gzipCalls } layout body page ∧
    DictionaryIndex.readIndices limits.indices (page.mask.count true) page.scalars = .ok indices ∧
    indices.map (fun index => entries[index]?) = (slots.filterMap id).map some ∧
    slots.map Option.isSome = page.mask ∧ slots.length = ByteArrayFallback.declaredSlots frame

def IndexPageWire {α : Type} := IndexPageWireWith (α := α) .snappy 0

/-- The fully expanded dictionary has the declared extent and round-trips
all PLAIN byte strings in original order, including unused entries. -/
def DictionaryWire (limits : Limits) (source : Bytes) (frame : Page.Frame) (entries : Array String) : Prop :=
  ∃ header expanded,
    frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧ header.numValues ≤ limits.maxDictionaryEntries ∧
    StoredWire (limits.dictionaryBounds frame).compressedLimit source frame ∧
    Payload.Decodes frame.value.uncompressedSize .snappy (Page.Checksum.payloadBytes source frame).toList expanded ∧
    expanded.length = frame.value.uncompressedSize ∧ expanded.length ≤ limits.expandedDictionaryBytes ∧
    expanded = Plain.ByteArray.wire (entries.toList.map Dictionary.octets) ∧ entries.size = header.numValues

/-- The original header gives the exact raw-level and compressed or raw
index windows. Nullable slots retain the original dictionary octets. -/
def PageWire (limits : Limits) (source : Bytes) (entries : Array String)
    (frame : Page.Frame) (slots : List (Option String)) : Prop :=
  let body := Page.Checksum.payloadBytes source frame
  ∃ (params : ScalarPage.Parameters) (layout : FlatPage.Layout) (page : ScalarPage.Prepared) (indices : List Nat),
    FlatColumn.pageParameters .optional Payload.Codec.snappy.id frame.value = some params ∧ params.encoding = 8 ∧
    StoredWire limits.file.column.maxPageBytes source frame ∧
    frame.value.uncompressedSize ≤ limits.maxExpandedPageBytes ∧
    ScalarPage.validateFor 8 params limits.scalar body = .ok layout ∧
    ScalarPage.PreparedWire params limits.scalar layout body page ∧
    DictionaryIndex.readIndices limits.indices (page.mask.count true) page.scalars = .ok indices ∧
    indices.map (fun index => entries[index]?) = (slots.filterMap id).map some ∧
    indices.map (fun index => (entries.map Dictionary.octets)[index]?) =
      (slots.filterMap id).map (some ∘ Dictionary.octets) ∧
    slots.map Option.isSome = page.mask ∧ slots.length = ByteArrayFallback.declaredSlots frame

def FramesWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (rows : Nat)
    (frames : List Page.Frame) (slots : List (Option String)) : Prop :=
  expandedBytes frames ≤ limits.maxExpandedChunkBytes ∧ (expandedBytes frames : Int) = metadata.totalUncompressedSize ∧
  ∃ dictionary data entries pages,
    frames = dictionary :: data ∧ metadata.dictionaryPageOffset = some (dictionary.header.start : Int) ∧
    data.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
    DictionaryWire limits source dictionary entries ∧ List.Forall₂ (PageWire limits source entries) data pages ∧
    slots = pages.flatten ∧ slots.length = rows

def GroupWire {name : String} (limits : Limits) (checked : Checked name) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option String)) : Prop :=
  ByteArrayFallback.BoundGroupWireWithCodec .snappy checked.physical.binding limits.toLimits
    (fun metadata source rows frames output =>
      (storedBytes frames : Int) = metadata.totalCompressedSize ∧
      storedBytes frames ≤ limits.file.column.maxChunkBytes ∧
      FramesWire limits metadata source rows frames output) index group slots

/-- The full selected source succeeds before native IPC limits are applied. -/
def convert (parquet : Limits) (ipc : Arrow.MixedFlat.Limits) (input : Bytes)
    (name : String) : Except Error KBytes := do
  let checked ← (Dictionary.openFile parquet.toLimits input name).mapError .openFile
  let groups ← ((List.range checked.physical.snapshot.groupCount).mapM (readGroup parquet checked)).mapError .column
  (Arrow.MixedFlat.OrderedWriter.emit ipc (Utf8.fields name .optional)
    (groups.map (Utf8.batch name .optional))).mapError .writer

end Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy
