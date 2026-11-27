module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Defs

/-! An opt-in dictionary-only GZIP V1 source for an opaque BYTE_ARRAY leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary

open Plain.ByteArray
open Arrow.BinaryView

structure Limits extends toSnappyLimits : Snappy.Limits where
  gzipCalls : Nat := 1024 * 1024

def readDictionary (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (frame : Page.Frame) : Except (FlatColumn.PageError Snappy.DecodeError) (Array Bytes) :=
  let decoded := Utf8.Dictionary.Snappy.readDictionaryBytesWith .gzip limits.gzipCalls
    limits.toSnappyLimits metadata source frame
  (decoded.map List.toArray).mapError (.decode ∘ .dictionary)

/-- The data frame itself must record RLE_DICTIONARY. A PLAIN fallback
page returns its original encoding at its original frame coordinate. -/
def decodePage (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (dictionary : Option (Array Bytes)) (frame : Page.Frame) :
    Except (FlatColumn.PageError Snappy.DecodeError) (List (Option Bytes)) :=
  match frame.value.kind with
  | .dataV1 header =>
    if header.encoding = 8 then
      let decoded := Utf8.Dictionary.Snappy.decodeIndexPageWith .gzip limits.gzipCalls
        limits.toSnappyLimits metadata source dictionary frame
      decoded.mapError (.decode ∘ .dictionary)
    else .error (.encoding header.encoding)
  | .dataV2 _ => .error .unsupportedVersion
  | .dictionary _ | .skipped _ => .error .unsupportedKind

def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except Snappy.GroupError (List (Option Bytes)) := do
  Utf8.Dictionary.Snappy.checkExpandedChunk limits.toSnappyLimits metadata group column name frames
  ByteArrayFallback.readFramesWith (readDictionary limits metadata source) (decodePage limits metadata source)
    metadata group column name rows frames

def readGroup {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat) :
    Except Snappy.GroupError (List (Option Bytes)) :=
  ByteArrayFallback.readBoundGroupWithCodec .gzip limits.maxExpandedChunkBytes .rleDictionary
    checked.physical.binding limits.toSnappyLimits.toLimits (readFrames limits) index

def PageWire (limits : Limits) (source : Bytes) (entries : Array Bytes)
    (frame : Page.Frame) (slots : List (Option Bytes)) : Prop :=
  (∃ header, frame.value.kind = .dataV1 header ∧ header.encoding = 8) ∧
    Utf8.Dictionary.Snappy.IndexPageWireWith .gzip limits.gzipCalls limits.toSnappyLimits source entries frame slots

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

end Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary
