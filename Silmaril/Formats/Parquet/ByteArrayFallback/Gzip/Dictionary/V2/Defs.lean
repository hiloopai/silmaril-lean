module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.Defs

/-! An opt-in dictionary-only GZIP V2 source for an opaque BYTE_ARRAY leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.V2

open Plain.ByteArray
open Arrow.BinaryView

abbrev Limits := Dictionary.Limits

/-- The data frame itself must record RLE_DICTIONARY. A PLAIN fallback
page returns its original encoding at its original frame coordinate. -/
def decodePage (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (dictionary : Option (Array Bytes)) (frame : Page.Frame) :
    Except (FlatColumn.PageError Snappy.DecodeError) (List (Option Bytes)) :=
  match frame.value.kind with
  | .dataV2 header =>
    if header.encoding = 8 then
      let decoded := Utf8.Dictionary.Snappy.decodeIndexPageWith .gzip limits.gzipCalls
        limits.toSnappyLimits metadata source dictionary frame
      decoded.mapError (.decode ∘ .dictionary)
    else .error (.encoding header.encoding)
  | .dataV1 _ => .error .unsupportedVersion
  | .dictionary _ | .skipped _ => .error .unsupportedKind

def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except Snappy.GroupError (List (Option Bytes)) := do
  Utf8.Dictionary.Snappy.checkExpandedChunk limits.toSnappyLimits metadata group column name frames
  ByteArrayFallback.readFramesWith (Dictionary.readDictionary limits metadata source) (decodePage limits metadata source)
    metadata group column name rows frames

def readGroup {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat) :
    Except Snappy.GroupError (List (Option Bytes)) :=
  ByteArrayFallback.readBoundGroupWithCodec .gzip limits.maxExpandedChunkBytes .rleDictionary
    checked.physical.binding limits.toSnappyLimits.toLimits (readFrames limits) index

def PageWire (limits : Limits) (source : Bytes) (entries : Array Bytes)
    (frame : Page.Frame) (slots : List (Option Bytes)) : Prop :=
  (∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 8) ∧
    Utf8.Dictionary.Snappy.IndexPageWireWith .gzip limits.gzipCalls limits.toSnappyLimits source entries frame slots

/-- The raw definition section precedes the exact flag-selected index suffix. -/
def SuffixWire (limits : Limits) (source : Bytes) (entries : Array Bytes)
    (frame : Page.Frame) (slots : List (Option Bytes)) : Prop :=
  ∃ (header : Page.DataV2) (layout : FlatPage.Layout) (definitions : Bytes) (stored : List UInt8)
      (decoded : Bytes) (indices : List Nat),
    frame.value.kind = .dataV2 header ∧ header.encoding = 8 ∧ header.repetitionBytes = 0 ∧
    header.definitionBytes ≤ frame.value.compressedSize ∧ header.definitionBytes ≤ frame.value.uncompressedSize ∧
    definitions.length = header.definitionBytes ∧
    (Page.Checksum.payloadBytes source frame).toList = definitions.toList ++ stored ∧
    FlatPage.readMask layout header.numValues limits.toSnappyLimits.scalar.levels definitions = .ok (slots.map Option.isSome) ∧
    (slots.map Option.isSome).count true = header.numValues - header.numNulls ∧
    stored.length = frame.value.compressedSize - header.definitionBytes ∧
    decoded.toList.length = frame.value.uncompressedSize - header.definitionBytes ∧
    (if header.isCompressed then Compression.Gzip.decoder stored = some (decoded.toList, [])
     else stored = decoded.toList) ∧
    DictionaryIndex.readIndices limits.toSnappyLimits.indices ((slots.map Option.isSome).count true) decoded = .ok indices ∧
    indices.map (fun index => entries[index]?) = (slots.filterMap id).map some

def FramesWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (rows : Nat)
    (frames : List Page.Frame) (slots : List (Option Bytes)) : Prop :=
  Utf8.Dictionary.Snappy.expandedBytes frames ≤ limits.maxExpandedChunkBytes ∧
  (Utf8.Dictionary.Snappy.expandedBytes frames : Int) = metadata.totalUncompressedSize ∧
  ∃ (dictionary : Page.Frame) (data : List Page.Frame) (entries : Array Bytes) (pages : List (List (Option Bytes))),
    frames = dictionary :: data ∧ metadata.dictionaryPageOffset = some (dictionary.header.start : Int) ∧
    data.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
    Utf8.Dictionary.Snappy.DictionaryBytesWireWith .gzip limits.toSnappyLimits source dictionary entries.toList ∧
    List.Forall₂ (PageWire limits source entries) data pages ∧ slots = pages.flatten ∧ slots.length = rows

def GroupWire {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option Bytes)) : Prop :=
  ByteArrayFallback.BoundGroupWireWithCodec .gzip checked.physical.binding limits.toSnappyLimits.toLimits
    (fun metadata source rows frames output =>
      (Utf8.Dictionary.Snappy.storedBytes frames : Int) = metadata.totalCompressedSize ∧
      Utf8.Dictionary.Snappy.storedBytes frames ≤ limits.file.column.maxChunkBytes ∧
      FramesWire limits metadata source rows frames output) index group slots

/-- Export the selected unannotated dictionary-only column through native EOS. -/
def convert (parquet : Limits) (ipc : Arrow.Limits) (view : Column.Limits) (input : Bytes)
    (name : String) : Except Snappy.Error KBytes :=
  Snappy.convertWith parquet.toSnappyLimits ipc view input name (readGroup parquet)

end Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.V2
