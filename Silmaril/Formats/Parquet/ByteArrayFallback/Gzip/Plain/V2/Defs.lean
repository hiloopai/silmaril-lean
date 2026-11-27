module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.V2.Defs

/-! Opt-in GZIP PLAIN V2 over a flat optional unannotated BYTE_ARRAY leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Plain.V2

open Arrow.BinaryView
open Silmaril.Formats.Parquet.Plain.ByteArray

abbrev Limits := Dictionary.Limits

/-- The original leading dictionary is outside this profile. -/
def rejectDictionary (_ : Page.Frame) : Except (FlatColumn.PageError Snappy.DecodeError) Unit :=
  .error .unsupportedKind

/-- Apply the original offset and count checks, then admit only PLAIN V2 data frames. -/
def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except Snappy.GroupError (List (Option Bytes)) := do
  Utf8.Dictionary.Snappy.checkExpandedChunk limits.toSnappyLimits metadata group column name frames
  ByteArrayFallback.readFramesWith rejectDictionary
    (fun _ => Fallback.V2.decodePlainPage limits metadata source) metadata group column name rows frames

def readGroup {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat) :
    Except Snappy.GroupError (List (Option Bytes)) :=
  ByteArrayFallback.readBoundGroupWithCodec .gzip limits.maxExpandedChunkBytes .rleDictionary
    checked.physical.binding limits.toSnappyLimits.toLimits (readFrames limits) index

abbrev PageWire := Fallback.V2.PlainPageWire

def FramesWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (rows : Nat)
    (frames : List Page.Frame) (slots : List (Option Bytes)) : Prop :=
  Utf8.Dictionary.Snappy.expandedBytes frames ≤ limits.maxExpandedChunkBytes ∧
  (Utf8.Dictionary.Snappy.expandedBytes frames : Int) = metadata.totalUncompressedSize ∧
  metadata.dictionaryPageOffset = none ∧
  frames.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
  ∃ pages, List.Forall₂ (PageWire limits source) frames pages ∧ slots = pages.flatten ∧ slots.length = rows

def GroupWire {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option Bytes)) : Prop :=
  ByteArrayFallback.BoundGroupWireWithCodec .gzip checked.physical.binding limits.toSnappyLimits.toLimits
    (fun metadata source rows frames output =>
      (Utf8.Dictionary.Snappy.storedBytes frames : Int) = metadata.totalCompressedSize ∧
      Utf8.Dictionary.Snappy.storedBytes frames ≤ limits.file.column.maxChunkBytes ∧
      FramesWire limits metadata source rows frames output) index group slots

/-- Export the selected opaque PLAIN groups through native BinaryView EOS. -/
def convert (parquet : Limits) (ipc : Arrow.Limits) (view : Column.Limits) (input : Bytes)
    (name : String) : Except Snappy.Error KBytes :=
  Snappy.convertWith parquet.toSnappyLimits ipc view input name (readGroup parquet)

end Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Plain.V2
