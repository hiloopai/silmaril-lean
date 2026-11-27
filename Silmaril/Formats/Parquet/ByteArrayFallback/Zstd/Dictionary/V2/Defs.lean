module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Defs
public import Silmaril.Formats.Parquet.FlatColumn.Zstd.Defs

/-! Opt-in Zstandard V2 dictionary-only over one flat optional unannotated BYTE_ARRAY. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2

open Plain.ByteArray
open Arrow.BinaryView

structure Limits extends toPhysical : Snappy.Limits where
  compression : FlatColumn.Zstd.CompressionLimits := ⟨8 * 1024 * 1024, 43690⟩

def Limits.page (limits : Limits) : FlatColumn.Zstd.Limits :=
  ⟨limits.file.column, limits.toPhysical.scalar, limits.compression⟩

inductive DecodeError where
  | unadvertisedEncoding (actual : Int)
  | dictionaryEntryLimit (maximum actual : Nat)
  | zstd (cause : FlatColumn.Zstd.Error)
  | entries (cause : Plain.Error)
  | missingDictionary
  | indices (cause : DictionaryIndex.Error)
  deriving DecidableEq, Repr

abbrev GroupError := FlatColumn.Error DecodeError

inductive Error where
  | openFile (cause : Snappy.OpenError)
  | column (cause : GroupError)
  | writer (cause : StreamWriter.Error)
  deriving DecidableEq, Repr

/-- The original leading PLAIN dictionary uses one whole-body Zstandard frame. -/
def readDictionary (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (frame : Page.Frame) : Except (FlatColumn.PageError DecodeError) (Array Bytes) := do
  let .dictionary header := frame.value.kind | throw .unsupportedKind
  if header.encoding ≠ 0 then throw (.encoding header.encoding)
  if !metadata.encodings.contains 0 then throw (.decode (.unadvertisedEncoding 0))
  if limits.maxDictionaryEntries < header.numValues then
    throw (.decode (.dictionaryEntryLimit limits.maxDictionaryEntries header.numValues))
  let bounds := limits.toPhysical.dictionaryBounds frame
  let _ ← (Page.Checksum.verify bounds.compressedLimit source frame).mapError .checksum
  let expanded ← (FlatColumn.Zstd.decodePayload limits.compression bounds Payload.Codec.zstd.id
    (Page.Checksum.payloadBytes source frame).toList).mapError (.decode ∘ .zstd)
  let entries ← (Plain.ByteArray.decode limits.toPhysical.entryBytes header.numValues (Bytes.ofList expanded))
    |>.mapError (.decode ∘ .entries)
  return entries.toArray

/-- Verify the whole stored body before reading raw levels and the flag-selected index suffix. -/
def decodePage (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (dictionary : Option (Array Bytes)) (frame : Page.Frame) :
    Except (FlatColumn.PageError DecodeError) (List (Option Bytes)) := do
  match frame.value.kind with
  | .dataV2 header =>
    if header.encoding ≠ 8 then throw (.encoding header.encoding)
    if !metadata.encodings.contains 8 then throw (.decode (.unadvertisedEncoding 8))
    let some entries := dictionary | throw (.decode .missingDictionary)
    let _ ← (Page.Checksum.verify limits.file.column.maxPageBytes source frame).mapError .checksum
    let some params := FlatColumn.pageParameters .optional Payload.Codec.zstd.id frame.value |
      throw .unsupportedKind
    let prepared ← (FlatColumn.Zstd.prepareFor 8 limits.page params (Page.Checksum.payloadBytes source frame))
      |>.mapError (.decode ∘ .zstd)
    let indices ← (DictionaryIndex.readIndices limits.toPhysical.indices (prepared.mask.count true) prepared.scalars)
      |>.mapError (.decode ∘ .indices)
    let values ← (DictionaryIndex.select entries indices).mapError (.decode ∘ .indices)
    (FlatPage.reconstruct prepared.mask values).mapError (.decode ∘ .indices ∘ .slots)
  | .dataV1 _ => throw .unsupportedVersion
  | .dictionary _ | .skipped _ => throw .unsupportedKind

def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except GroupError (List (Option Bytes)) := do
  Utf8.Dictionary.Snappy.checkExpandedChunk limits.toPhysical metadata group column name frames
  ByteArrayFallback.readFramesWith (readDictionary limits metadata source) (decodePage limits metadata source)
    metadata group column name rows frames

def readGroup {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat) :
    Except GroupError (List (Option Bytes)) :=
  ByteArrayFallback.readBoundGroupWithCodec .zstd limits.maxExpandedChunkBytes .rleDictionary
    checked.physical.binding limits.toPhysical.toLimits (readFrames limits) index

/-- One checked frame accounts for the complete dictionary and its exact PLAIN bytes. -/
def DictionaryWire (limits : Limits) (source : Bytes) (frame : Page.Frame) (entries : Array Bytes) : Prop :=
  let bounds := limits.toPhysical.dictionaryBounds frame
  ∃ header, frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
    header.numValues ≤ limits.maxDictionaryEntries ∧ entries.size = header.numValues ∧
    Utf8.Dictionary.Snappy.StoredWire bounds.compressedLimit source frame ∧
    FlatColumn.Zstd.PayloadWire limits.compression bounds Payload.Codec.zstd.id
      (Page.Checksum.payloadBytes source frame).toList (Plain.ByteArray.wire entries.toList)

/-- The original raw levels and flag-selected index stream account for every nullable slot. -/
def PageWire (limits : Limits) (source : Bytes) (entries : Array Bytes)
    (frame : Page.Frame) (slots : List (Option Bytes)) : Prop :=
  Utf8.Dictionary.Snappy.StoredWire limits.file.column.maxPageBytes source frame ∧
  frame.value.uncompressedSize ≤ limits.maxExpandedPageBytes ∧
  ∃ (data : Page.DataV2) (layout : FlatPage.Layout) (definitions : Bytes) (encoded : List UInt8)
      (decoded : Bytes) (indices : List Nat),
    frame.value.kind = .dataV2 data ∧ data.encoding = 8 ∧ data.repetitionBytes = 0 ∧
    data.numRows = data.numValues ∧ data.numNulls ≤ data.numValues ∧
    data.definitionBytes ≤ frame.value.compressedSize ∧ data.definitionBytes ≤ frame.value.uncompressedSize ∧
    data.definitionBytes ≤ limits.page.scalar.levels.bytes ∧ definitions.length = data.definitionBytes ∧
    (Page.Checksum.payloadBytes source frame).toList = definitions.toList ++ encoded ∧
    FlatPage.readMask layout data.numValues limits.page.scalar.levels definitions = .ok (slots.map Option.isSome) ∧
    (slots.map Option.isSome).count true = data.numValues - data.numNulls ∧
    slots.length = data.numValues ∧
    FlatColumn.Zstd.PayloadWire limits.compression
      (limits.page.scalar.payloadBounds ⟨frame.value.compressedSize, frame.value.uncompressedSize⟩ data.definitionBytes)
      (ScalarPage.v2Codec Payload.Codec.zstd.id (some data.isCompressed)) encoded decoded.toList ∧
    DictionaryIndex.readIndices limits.toPhysical.indices ((slots.map Option.isSome).count true) decoded = .ok indices ∧
    indices.map (fun index => entries[index]?) = (slots.filterMap id).map some

def FramesWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (rows : Nat)
    (frames : List Page.Frame) (slots : List (Option Bytes)) : Prop :=
  Utf8.Dictionary.Snappy.expandedBytes frames ≤ limits.maxExpandedChunkBytes ∧
  (Utf8.Dictionary.Snappy.expandedBytes frames : Int) = metadata.totalUncompressedSize ∧
  ∃ (dictionary : Page.Frame) (data : List Page.Frame) (entries : Array Bytes) (pages : List (List (Option Bytes))),
    frames = dictionary :: data ∧ metadata.dictionaryPageOffset = some (dictionary.header.start : Int) ∧
    data.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
    DictionaryWire limits source dictionary entries ∧
    List.Forall₂ (PageWire limits source entries) data pages ∧ slots = pages.flatten ∧ slots.length = rows

def GroupWire {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option Bytes)) : Prop :=
  ByteArrayFallback.BoundGroupWireWithCodec .zstd checked.physical.binding limits.toPhysical.toLimits
    (fun metadata source rows frames output =>
      (Utf8.Dictionary.Snappy.storedBytes frames : Int) = metadata.totalCompressedSize ∧
      Utf8.Dictionary.Snappy.storedBytes frames ≤ limits.file.column.maxChunkBytes ∧
      FramesWire limits metadata source rows frames output) index group slots

/-- Emit native BinaryView only after all selected groups succeed. -/
def convert (parquet : Limits) (ipc : Arrow.Limits) (view : Column.Limits) (input : Bytes)
    (name : String) : Except Error KBytes := do
  let checked ← (Snappy.openFile parquet.toPhysical input name).mapError .openFile
  let groups ← ((List.range checked.physical.snapshot.groupCount).mapM (readGroup parquet checked)).mapError .column
  let source : ToIpc.Source := ⟨⟨name, true⟩, groups⟩
  (StreamWriter.emit ipc view source.ipcField source.batches).mapError .writer

end Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2
