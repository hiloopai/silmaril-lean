module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Defs

/-! Opt-in Snappy STRING with one original dictionary-to-PLAIN transition. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy

abbrev Limits := Dictionary.Snappy.Limits
abbrev Checked (name : String) := Dictionary.Checked name

inductive DecodeError where
  | dictionary (cause : FlatColumn.PageError Dictionary.Snappy.DecodeError)
  | unadvertisedPlain
  | expandedPageLimit
  | checksum (cause : Page.Checksum.Error)
  | plain (cause : ScalarPage.Error)
  | invalidPlainText (slot : Nat)
  | dictionaryAfterPlain
  | missingDictionary
  deriving DecidableEq, Repr

abbrev GroupError := FlatColumn.Error DecodeError

inductive Error where
  | openFile (cause : Utf8.Error)
  | column (cause : GroupError)
  | writer (cause : Arrow.MixedFlat.OrderedWriter.Error)
  deriving DecidableEq, Repr

def plainLimits (limits : Limits) : Plain.ByteArray.Limits :=
  ⟨limits.maxExpandedPageBytes, limits.file.maxValueBytes⟩

/-- Check the whole stored body before decoding PLAIN and validating every
present slot in original page-relative logical row order. -/
def decodePlain (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (frame : Page.Frame) : Except (FlatColumn.PageError DecodeError) (List (Option String)) := do
  let some params := FlatColumn.pageParameters .optional Payload.Codec.snappy.id frame.value |
    throw .unsupportedKind
  if !metadata.encodings.contains 0 then .error (.decode .unadvertisedPlain)
  else if limits.maxExpandedPageBytes < params.sizes.uncompressed then .error (.decode .expandedPageLimit)
  else do
    let _ ← (Page.Checksum.verify limits.file.column.maxPageBytes source frame).mapError (.decode ∘ .checksum)
    let raw ← (ScalarPage.decode (.byteArray (plainLimits limits)) params limits.scalar
      (Page.Checksum.payloadBytes source frame)).mapError (.decode ∘ .plain)
    (Utf8.decodeSlotsWith DecodeError.invalidPlainText raw).mapError .decode

/-- Dispatch by the original tag after the chunk's one-way phase check. -/
def decodeData (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (dictionary : Option (Array String)) (frame : Page.Frame) :
    Except (FlatColumn.PageError DecodeError) (List (Option String)) := do
  let some entries := dictionary | throw (.decode .missingDictionary)
  match Fallback.dataEncoding frame with
  | some 8 =>
    (Dictionary.Snappy.decodePage limits metadata source (some entries) frame).mapError (.decode ∘ .dictionary)
  | some 0 => decodePlain limits metadata source frame
  | some actual => throw (.encoding actual)
  | none => throw .unsupportedKind

def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except GroupError (List (Option String)) := do
  Dictionary.Snappy.checkExpandedChunk limits metadata group column name frames
  let (dictionary, data) := ByteArrayFallback.splitLeading frames
  Fallback.checkPhasesWith DecodeError.dictionaryAfterPlain group column name (if dictionary.isSome then 1 else 0) data
  ByteArrayFallback.readFramesWith
    (fun frame => (Dictionary.Snappy.readDictionary limits metadata source frame).mapError (.decode ∘ .dictionary))
    (decodeData limits metadata source) metadata group column name rows frames

def readGroup {name : String} (limits : Limits) (checked : Checked name) (index : Nat) :
    Except GroupError (List (Option String)) :=
  ByteArrayFallback.readBoundGroupWithCodec .snappy limits.maxExpandedChunkBytes .rleDictionary
    checked.physical.binding limits.toLimits (readFrames limits) index

/-- Exact original frame, raw levels or V1 body, and PLAIN UTF-8 octets. -/
def PlainPageWire (limits : Limits) (source : Bytes) (frame : Page.Frame) (slots : List (Option String)) : Prop :=
  let body := Page.Checksum.payloadBytes source frame
  ∃ (params : ScalarPage.Parameters) (layout : FlatPage.Layout) (page : ScalarPage.Prepared),
    FlatColumn.pageParameters .optional Payload.Codec.snappy.id frame.value = some params ∧
    Dictionary.Snappy.StoredWire limits.file.column.maxPageBytes source frame ∧
    params.sizes.uncompressed ≤ limits.maxExpandedPageBytes ∧
    ScalarPage.validate params limits.scalar body = .ok layout ∧
    ScalarPage.PreparedWire params limits.scalar layout body page ∧ slots.map Option.isSome = page.mask ∧
    page.scalars.toList = Plain.ByteArray.wire ((slots.filterMap id).map Dictionary.octets) ∧
    slots.length = ByteArrayFallback.declaredSlots frame

def PageWire (limits : Limits) (source : Bytes) (entries : Array String)
    (frame : Page.Frame) (slots : List (Option String)) : Prop :=
  (Fallback.dataEncoding frame = some 8 ∧ Dictionary.Snappy.PageWire limits source entries frame slots) ∨
    (Fallback.dataEncoding frame = some 0 ∧ PlainPageWire limits source frame slots)

def FramesWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (rows : Nat)
    (frames : List Page.Frame) (slots : List (Option String)) : Prop :=
  Dictionary.Snappy.expandedBytes frames ≤ limits.maxExpandedChunkBytes ∧
  (Dictionary.Snappy.expandedBytes frames : Int) = metadata.totalUncompressedSize ∧
  ∃ dictionary data entries pages,
    frames = dictionary :: data ∧ metadata.dictionaryPageOffset = some (dictionary.header.start : Int) ∧
    data.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
    Dictionary.Snappy.DictionaryWire limits source dictionary entries ∧ Fallback.Phases data ∧
    List.Forall₂ (PageWire limits source entries) data pages ∧ slots = pages.flatten ∧ slots.length = rows

def GroupWire {name : String} (limits : Limits) (checked : Checked name) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option String)) : Prop :=
  ByteArrayFallback.BoundGroupWireWithCodec .snappy checked.physical.binding limits.toLimits
    (fun metadata source rows frames output =>
      (Dictionary.Snappy.storedBytes frames : Int) = metadata.totalCompressedSize ∧
      Dictionary.Snappy.storedBytes frames ≤ limits.file.column.maxChunkBytes ∧
      FramesWire limits metadata source rows frames output) index group slots

/-- Finish all selected source groups before applying the native IPC limits. -/
def convert (parquet : Limits) (ipc : Arrow.MixedFlat.Limits) (input : Bytes)
    (name : String) : Except Error KBytes := do
  let checked ← (Dictionary.openFile parquet.toLimits input name).mapError .openFile
  let groups ← ((List.range checked.physical.snapshot.groupCount).mapM (readGroup parquet checked)).mapError .column
  (Arrow.MixedFlat.OrderedWriter.emit ipc (Utf8.fields name .optional)
    (groups.map (Utf8.batch name .optional))).mapError .writer

end Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy
