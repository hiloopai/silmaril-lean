module

public import Silmaril.Formats.Parquet.DictionaryIndex.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.File.Defs

/-! One selected flat optional BYTE_ARRAY chunk with an optional leading
dictionary and explicit RLE_DICTIONARY or PLAIN data-page dispatch. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback

/-- Select the observed dictionary and data header contract for a chunk. -/
inductive Profile where
  | rleDictionary
  | plainDictionaryV1
  deriving DecidableEq, Repr

def Profile.dictionaryTag : Profile → Int
  | .rleDictionary => 0
  | .plainDictionaryV1 => 2

def Profile.dataTag : Profile → Int
  | .rleDictionary => 8
  | .plainDictionaryV1 => 2

def Profile.advertised : Profile → Int → Bool
  | .rleDictionary, tag => tag == 0 || tag == 3 || tag == 8
  | .plainDictionaryV1, tag => tag == 0 || tag == 2 || tag == 3 || tag == 4

/-- The legacy writer labels the absent repetition section BIT_PACKED.
The checked flat leaf has maximum repetition level zero. Only that
absent section's tag is normalized for the existing RLE scalar adapter. -/
def Profile.parameters (profile : Profile) (header : Page.Header) : Option ScalarPage.Parameters :=
  match profile with
  | .rleDictionary => FlatColumn.pageParameters .optional 0 header
  | .plainDictionaryV1 => do
    let params ← FlatColumn.pageParameters .optional 0 header
    let .v1 definitions repetitions := params.version | none
    if definitions = 3 ∧ repetitions = 4 then some { params with version := .v1 3 3 }
    else none

structure Limits where
  file : Plain.ByteArray.File.Limits := {}
  maxDictionaryEntries : Nat := 1024 * 1024
  maxDictionaryBytes : Nat := 4 * 1024 * 1024

def Limits.dictionary (limits : Limits) : Plain.ByteArray.Limits :=
  ⟨min limits.maxDictionaryBytes limits.file.column.maxPageBytes, limits.file.maxValueBytes⟩

def Limits.indices (limits : Limits) : Hybrid.Limits :=
  ⟨limits.file.column.maxRows, limits.file.column.maxPageBytes⟩

inductive DecodeError where
  | missingDictionary
  | dictionaryEncoding (actual : Int)
  | unadvertisedEncoding (actual : Int)
  | dictionaryEntryLimit (maximum actual : Nat)
  | dictionaryBody (reason : Plain.Error)
  | plain (reason : ScalarPage.Error)
  | indices (reason : DictionaryIndex.Error)
  deriving DecidableEq, Repr

abbrev Error := FlatColumn.Error DecodeError
abbrev Checked (name : String) := Plain.ByteArray.File.Checked name .optional

/-- Bind the existing checked byte-array selection, with its file and total
row caps. The per-group profile is selected separately by `readGroup`. -/
def openFile (limits : Limits) (input : Bytes) (name : String) :
    Except Plain.ByteArray.File.Error (Checked name) :=
  Plain.ByteArray.File.openFile limits.file input name .optional

def locateForCodec (codec : Payload.Codec) (expandedChunkCap : Nat) (profile : Profile) (limits : Limits)
    (leaf : Footer.SchemaElement) (group : Footer.RowGroup)
    (metadata : Footer.ColumnMetadata) (footerStart : Nat) : Except FlatColumn.ColumnError Footer.Span :=
  if ¬ (metadata.pathInSchema = [leaf.name] ∧ metadata.physicalType = .byteArray ∧
      metadata.numValues = group.numRows) then .error .association
  else if metadata.codec ≠ codec.id then .error (.codec metadata.codec)
  else if !metadata.encodings.all profile.advertised then .error .encodings
  else if metadata.indexPageOffset.isSome then .error .unsupportedOffsets
  else if metadata.totalCompressedSize > (limits.file.column.maxChunkBytes : Int) ||
      metadata.totalUncompressedSize > (expandedChunkCap : Int) then .error .chunkLimit
  else
    match Page.columnSpan footerStart metadata with
    | none => .error .bounds
    | some span => .ok span

def locateFor (profile : Profile) (limits : Limits) :=
  locateForCodec .uncompressed limits.file.column.maxChunkBytes profile limits

def splitLeading : List Page.Frame → Option Page.Frame × List Page.Frame
  | frame :: rest =>
    match frame.value.kind with
    | .dictionary _ => (some frame, rest)
    | _ => (none, frame :: rest)
  | [] => (none, [])

def bodyLimits (maxBytes : Nat) (header : Page.Header) : Except (FlatColumn.PageError DecodeError) Unit :=
  if header.crc ≠ none then .error .crcUnsupported
  else if maxBytes < header.compressedSize ∨ maxBytes < header.uncompressedSize then .error .byteLimit
  else if header.compressedSize ≠ header.uncompressedSize then .error .sizeMismatch
  else .ok ()

/-- Decode exact PLAIN length-prefixed entries in original dictionary order.
Both entry count and byte caps apply before the slice is copied. -/
def readDictionaryFor (profile : Profile) (limits : Limits) (metadata : Footer.ColumnMetadata)
    (source : Bytes) (frame : Page.Frame) :
    Except (FlatColumn.PageError DecodeError) (Array Bytes) := do
  let .dictionary header := frame.value.kind | throw .unsupportedKind
  bodyLimits limits.dictionary.totalBytes frame.value
  if header.encoding ≠ profile.dictionaryTag then .error (.decode (.dictionaryEncoding header.encoding))
  else if !metadata.encodings.contains profile.dictionaryTag then .error (.decode (.unadvertisedEncoding profile.dictionaryTag))
  else if limits.maxDictionaryEntries < header.numValues then
    .error (.decode (.dictionaryEntryLimit limits.maxDictionaryEntries header.numValues))
  else do
    let body := FlatColumn.frameBody source frame
    let entries ← (Plain.ByteArray.decode limits.dictionary header.numValues body).mapError (.decode ∘ .dictionaryBody)
    return entries.toArray

def decodeDataFor (profile : Profile) (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (dictionary : Option (Array Bytes)) (frame : Page.Frame) :
    Except (FlatColumn.PageError DecodeError) (List (Option Bytes)) := do
  bodyLimits limits.file.column.maxPageBytes frame.value
  let some params := profile.parameters frame.value |
    if (FlatColumn.pageParameters .optional 0 frame.value).isSome then throw .levels
    else throw .unsupportedKind
  let cap := min limits.file.column.maxRows (Hybrid.runLimit - 1)
  if params.encoding ≠ 0 ∧ params.encoding ≠ profile.dataTag then .error (.encoding params.encoding)
  else if !metadata.encodings.contains params.encoding then .error (.decode (.unadvertisedEncoding params.encoding))
  else if cap < params.numValues then .error (.slotLimit cap params.numValues)
  else if params.encoding = 0 then
    (ScalarPage.decode (.byteArray limits.file.values) params limits.file.scalar
      (FlatColumn.frameBody source frame)).mapError (.decode ∘ .plain)
  else do
    let some entries := dictionary | throw (.decode .missingDictionary)
    (DictionaryIndex.decode entries params limits.file.scalar limits.indices
      (FlatColumn.frameBody source frame)).mapError (.decode ∘ .indices)

def declaredSlots (frame : Page.Frame) : Nat :=
  ((FlatColumn.pageParameters .optional 0 frame.value).map (·.numValues)).getD 0

/-- Check original dictionary and data offsets and the full declared slot count
before invoking the chunk-local dictionary and ordered data callbacks. -/
def readFramesWith {δ α ε : Type}
    (openDictionary : Page.Frame → Except (FlatColumn.PageError ε) δ)
    (decodePage : Option δ → Page.Frame → Except (FlatColumn.PageError ε) (List (Option α)))
    (metadata : Footer.ColumnMetadata) (group column : Nat) (name : String) (rows : Nat)
    (frames : List Page.Frame) : Except (FlatColumn.Error ε) (List (Option α)) := do
  let failColumn := FlatColumn.Error.column group column name
  let failPage := fun (page : Nat) (frame : Page.Frame) =>
    FlatColumn.Error.page group column name page frame.header.start
  let (dictionary, data) := splitLeading frames
  let declared := (data.map declaredSlots).sum
  if dictionary.map (fun frame => (frame.header.start : Int)) ≠ metadata.dictionaryPageOffset ∨
      data.head?.map (fun frame => (frame.header.start : Int)) ≠ some metadata.dataPageOffset then
    .error (failColumn .unsupportedOffsets)
  else if declared ≠ rows then .error (failColumn (.declaredCount rows declared))
  else do
    let entries ← dictionary.mapM fun frame => (openDictionary frame).mapError (failPage 0 frame)
    let pages ← (data.zipIdx (if dictionary.isSome then 1 else 0)).mapM fun (frame, ordinal) =>
      (decodePage entries frame).mapError (failPage ordinal frame)
    return pages.flatten

def readFramesFor (profile : Profile) (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except Error (List (Option Bytes)) :=
  readFramesWith (readDictionaryFor profile limits metadata source)
    (decodeDataFor profile limits metadata source) metadata group column name rows frames

/-- Frame the selected chunk from the same snapshot as the binding, then
pass the original frames to the chunk-local reader. -/
def readBoundGroupWithCodec {snapshot : Snapshot.Checked} {name : String} {α ε : Type}
    (codec : Payload.Codec) (expandedChunkCap : Nat) (profile : Profile) (binding : FlatColumn.Binding snapshot ⟨name, .byteArray, .optional⟩)
    (limits : Limits)
    (read : Footer.ColumnMetadata → Bytes → Nat → Nat → String → Nat → List Page.Frame →
      Except (FlatColumn.Error ε) (List (Option α)))
    (index : Nat) : Except (FlatColumn.Error ε) (List (Option α)) := do
  let ordinal := binding.columnOrdinal
  let failColumn := FlatColumn.Error.column index ordinal name
  let some group := snapshot.groupAt index | throw (.groupIndex index)
  let rows := group.numRows.toNat
  if limits.file.column.maxRows < rows then .error (failColumn (.rowLimit limits.file.column.maxRows rows))
  else do
    let some column := group.columns[ordinal]? | throw (failColumn .missing)
    let metadata := column.metadata
    let span ← (locateForCodec codec expandedChunkCap profile limits binding.leaf group metadata
      snapshot.footer.start).mapError failColumn
    let frames ← (Page.readChunk limits.file.column.framing snapshot.bytes span).mapError (failColumn ∘ .framing)
    read metadata snapshot.bytes index ordinal name rows frames

def readBoundGroupWith {snapshot : Snapshot.Checked} {name : String} {α ε : Type}
    (profile : Profile) (binding : FlatColumn.Binding snapshot ⟨name, .byteArray, .optional⟩)
    (limits : Limits)
    (read : Footer.ColumnMetadata → Bytes → Nat → Nat → String → Nat → List Page.Frame →
      Except (FlatColumn.Error ε) (List (Option α))) (index : Nat) : Except (FlatColumn.Error ε) (List (Option α)) :=
  readBoundGroupWithCodec .uncompressed limits.file.column.maxChunkBytes profile binding limits read index

/-- Read the selected group from the same snapshot as its binding. Dictionary
state is local to this chunk and publication waits for all frames to succeed. -/
def readBoundGroupFor (profile : Profile) {snapshot : Snapshot.Checked} {name : String}
    (binding : FlatColumn.Binding snapshot ⟨name, .byteArray, .optional⟩) (limits : Limits) (index : Nat) :
    Except Error (List (Option Bytes)) :=
  readBoundGroupWith profile binding limits (readFramesFor profile limits) index

def readGroupFor (profile : Profile) {name : String} (checked : Checked name) (limits : Limits)
    (index : Nat) : Except Error (List (Option Bytes)) :=
  readBoundGroupFor profile checked.binding limits index

/-- Every present dictionary entry is the result of an exact bounded PLAIN
stream from the original leading frame. -/
def DictionaryWireFor (profile : Profile) (limits : Limits) (source : Bytes)
    (frame : Page.Frame) (entries : Array Bytes) : Prop :=
  ∃ header values,
    frame.value.kind = .dictionary header ∧ header.encoding = profile.dictionaryTag ∧
    frame.value.crc = none ∧ frame.value.compressedSize = frame.value.uncompressedSize ∧
    header.numValues ≤ limits.maxDictionaryEntries ∧ frame.value.compressedSize ≤ limits.dictionary.totalBytes ∧
    Plain.ByteArray.decode limits.dictionary header.numValues (FlatColumn.frameBody source frame) = .ok values ∧
    values.length = header.numValues ∧ (FlatColumn.frameBody source frame).toList = Plain.ByteArray.wire values ∧
    entries = values.toArray

/-- A frame's own typed header selects its checked body interpretation. The
dictionary branch uses only entries from this chunk's leading frame. -/
def PageWireFor (profile : Profile) (limits : Limits) (source : Bytes) (dictionary : Option (Array Bytes))
    (frame : Page.Frame) (slots : List (Option Bytes)) : Prop :=
  let body := FlatColumn.frameBody source frame
  ∃ params : ScalarPage.Parameters, ∃ layout : FlatPage.Layout, ∃ page : ScalarPage.Prepared,
    profile.parameters frame.value = some params ∧
    ScalarPage.validateFor params.encoding params limits.file.scalar body = .ok layout ∧
    ScalarPage.PreparedWire params limits.file.scalar layout body page ∧
    slots.map Option.isSome = page.mask ∧ slots.length = declaredSlots frame ∧
    ((params.encoding = 0 ∧ page.scalars.toList = Plain.ByteArray.wire (slots.filterMap id)) ∨
      (params.encoding = profile.dataTag ∧ ∃ entries indices, dictionary = some entries ∧
        DictionaryIndex.readIndices limits.indices (page.mask.count true) page.scalars = .ok indices ∧
        indices.map (fun index => entries[index]?) = (slots.filterMap id).map some))

def LeadingWireFor (profile : Profile) (limits : Limits) (source : Bytes) :
    Option Page.Frame → Option (Array Bytes) → Prop
  | none, none => True
  | some frame, some entries => DictionaryWireFor profile limits source frame entries
  | _, _ => False

def FramesWireFor (profile : Profile) (limits : Limits) (source : Bytes) (metadata : Footer.ColumnMetadata)
    (rows : Nat) (frames : List Page.Frame) (slots : List (Option Bytes)) : Prop :=
  ∃ dictionary data entries pages,
    frames = dictionary.toList ++ data ∧
    dictionary.map (fun frame : Page.Frame => (frame.header.start : Int)) = metadata.dictionaryPageOffset ∧
    data.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
    LeadingWireFor profile limits source dictionary entries ∧
    List.Forall₂ (PageWireFor profile limits source entries) data pages ∧ slots = pages.flatten ∧ slots.length = rows

/-- Attach a chunk-level relation to the selected original frames. -/
def BoundGroupWireWithCodec {snapshot : Snapshot.Checked} {name : String} {α : Type}
    (codec : Payload.Codec) (binding : FlatColumn.Binding snapshot ⟨name, .byteArray, .optional⟩) (limits : Limits)
    (wire : Footer.ColumnMetadata → Bytes → Nat → List Page.Frame → List (Option α) → Prop)
    (index : Nat) (group : Footer.RowGroup) (slots : List (Option α)) : Prop :=
  ∃ column span frames,
    snapshot.metadata.schema[binding.leafOrdinal]? = some binding.leaf ∧
    snapshot.groupAt index = some group ∧
    group.columns[binding.columnOrdinal]? = some column ∧
    column.metadata.pathInSchema = [binding.leaf.name] ∧ column.metadata.physicalType = .byteArray ∧
    column.metadata.numValues = group.numRows ∧ column.metadata.codec = codec.id ∧
    Page.columnSpan snapshot.footer.start column.metadata = some span ∧
    Page.readChunk limits.file.column.framing snapshot.bytes span = .ok frames ∧
    wire column.metadata snapshot.bytes group.numRows.toNat frames slots

def BoundGroupWireWith {snapshot : Snapshot.Checked} {name : String} {α : Type}
    (binding : FlatColumn.Binding snapshot ⟨name, .byteArray, .optional⟩) (limits : Limits)
    (wire : Footer.ColumnMetadata → Bytes → Nat → List Page.Frame → List (Option α) → Prop)
    (index : Nat) (group : Footer.RowGroup) (slots : List (Option α)) : Prop :=
  BoundGroupWireWithCodec .uncompressed binding limits wire index group slots

def BoundGroupWireFor (profile : Profile) {snapshot : Snapshot.Checked} {name : String}
    (binding : FlatColumn.Binding snapshot ⟨name, .byteArray, .optional⟩) (limits : Limits)
    (index : Nat) (group : Footer.RowGroup) (slots : List (Option Bytes)) : Prop :=
  BoundGroupWireWith binding limits (fun metadata source => FramesWireFor profile limits source metadata)
    index group slots

def GroupWireFor (profile : Profile) {name : String} (checked : Checked name) (limits : Limits)
    (index : Nat) (slots : List (Option Bytes)) : Prop :=
  ∃ group, BoundGroupWireFor profile checked.binding limits index group slots

/-- The existing tag-8/PLAIN profile keeps its public entry points. -/
def locate := locateFor .rleDictionary
def readDictionary := readDictionaryFor .rleDictionary
def decodeData := decodeDataFor .rleDictionary
def readFrames := readFramesFor .rleDictionary
def readGroup {name : String} := readGroupFor .rleDictionary (name := name)

def DictionaryWire := DictionaryWireFor .rleDictionary
def PageWire := PageWireFor .rleDictionary
def LeadingWire := LeadingWireFor .rleDictionary
def FramesWire := FramesWireFor .rleDictionary
def GroupWire {name : String} := GroupWireFor .rleDictionary (name := name)

/-- Opt in to the parquet-java V1 tag-2 dictionary and tag-2/PLAIN pages. -/
def readLegacyGroup {name : String} := readGroupFor .plainDictionaryV1 (name := name)

end Silmaril.Formats.Parquet.ByteArrayFallback
