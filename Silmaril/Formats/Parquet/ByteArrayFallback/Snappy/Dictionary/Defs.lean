module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Defs

/-! An opt-in dictionary-only Snappy source for an opaque BYTE_ARRAY leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Dictionary

open Plain.ByteArray
open Arrow.BinaryView

/-- The data frame itself must record RLE_DICTIONARY. A PLAIN fallback
page returns its original encoding at its original frame coordinate. -/
def decodePage (limits : Snappy.Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (dictionary : Option (Array Bytes)) (frame : Page.Frame) :
    Except (FlatColumn.PageError Snappy.DecodeError) (List (Option Bytes)) :=
  match Utf8.Fallback.dataEncoding frame with
  | some 8 => (Utf8.Dictionary.Snappy.decodeIndexPage limits metadata source dictionary frame).mapError
      (FlatColumn.PageError.decode ∘ Snappy.DecodeError.dictionary)
  | some actual => .error (.encoding actual)
  | none => .error .unsupportedKind

def readFrames (limits : Snappy.Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except Snappy.GroupError (List (Option Bytes)) := do
  Utf8.Dictionary.Snappy.checkExpandedChunk limits metadata group column name frames
  ByteArrayFallback.readFramesWith (Snappy.readDictionary limits metadata source) (decodePage limits metadata source)
    metadata group column name rows frames

def readGroup {name : String} (limits : Snappy.Limits) (checked : Snappy.Checked name) (index : Nat) :
    Except Snappy.GroupError (List (Option Bytes)) :=
  ByteArrayFallback.readBoundGroupWithCodec .snappy limits.maxExpandedChunkBytes .rleDictionary
    checked.physical.binding limits.toLimits (readFrames limits) index

def PageWire (limits : Snappy.Limits) (source : Bytes) (entries : Array Bytes)
    (frame : Page.Frame) (slots : List (Option Bytes)) : Prop :=
  Utf8.Fallback.dataEncoding frame = some 8 ∧ Utf8.Dictionary.Snappy.IndexPageWire limits source entries frame slots

def FramesWire (limits : Snappy.Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (rows : Nat)
    (frames : List Page.Frame) (slots : List (Option Bytes)) : Prop :=
  Utf8.Dictionary.Snappy.expandedBytes frames ≤ limits.maxExpandedChunkBytes ∧
  (Utf8.Dictionary.Snappy.expandedBytes frames : Int) = metadata.totalUncompressedSize ∧
  ∃ (dictionary : Page.Frame) (data : List Page.Frame) (entries : Array Bytes) (pages : List (List (Option Bytes))),
    frames = dictionary :: data ∧ metadata.dictionaryPageOffset = some (dictionary.header.start : Int) ∧
    data.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
    Utf8.Dictionary.Snappy.DictionaryBytesWire limits source dictionary entries.toList ∧
    List.Forall₂ (PageWire limits source entries) data pages ∧ slots = pages.flatten ∧ slots.length = rows

def GroupWire {name : String} (limits : Snappy.Limits) (checked : Snappy.Checked name) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option Bytes)) : Prop :=
  ByteArrayFallback.BoundGroupWireWithCodec .snappy checked.physical.binding limits.toLimits
    (fun metadata source rows frames output =>
      (Utf8.Dictionary.Snappy.storedBytes frames : Int) = metadata.totalCompressedSize ∧
      Utf8.Dictionary.Snappy.storedBytes frames ≤ limits.file.column.maxChunkBytes ∧
      FramesWire limits metadata source rows frames output) index group slots

/-- Export the selected unannotated dictionary-only column through native EOS. -/
def convert (parquet : Snappy.Limits) (ipc : Arrow.Limits) (view : Column.Limits) (input : Bytes)
    (name : String) : Except Snappy.Error KBytes :=
  Snappy.convertWith parquet ipc view input name (readGroup parquet)

end Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Dictionary
