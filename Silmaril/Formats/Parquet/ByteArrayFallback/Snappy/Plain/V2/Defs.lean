module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Defs

/-! Opt-in Snappy PLAIN V2 over a flat optional unannotated BYTE_ARRAY leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2

open Arrow.BinaryView
open Silmaril.Formats.Parquet.Plain.ByteArray

abbrev Limits := Snappy.Limits

/-- Admit only the original PLAIN V2 tag before invoking the shared opaque decoder. -/
def decodePage (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (frame : Page.Frame) : Except (FlatColumn.PageError Snappy.DecodeError) (List (Option Bytes)) :=
  match frame.value.kind with
  | .dataV2 header =>
    if header.encoding = 0 then
      (Utf8.Fallback.Snappy.decodePlainBytes limits metadata source frame).mapError (.decode ∘ .plain)
    else .error (.encoding header.encoding)
  | .dataV1 _ => .error .unsupportedVersion
  | .dictionary _ | .skipped _ => .error .unsupportedKind

/-- The original leading dictionary is outside this profile. -/
def rejectDictionary (_ : Page.Frame) : Except (FlatColumn.PageError Snappy.DecodeError) Unit :=
  .error .unsupportedKind

/-- Apply the original offset and count checks, then admit only PLAIN V2 data frames. -/
def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except Snappy.GroupError (List (Option Bytes)) := do
  Utf8.Dictionary.Snappy.checkExpandedChunk limits metadata group column name frames
  ByteArrayFallback.readFramesWith rejectDictionary
    (fun _ => decodePage limits metadata source) metadata group column name rows frames

def readGroup {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat) :
    Except Snappy.GroupError (List (Option Bytes)) :=
  ByteArrayFallback.readBoundGroupWithCodec .snappy limits.maxExpandedChunkBytes .rleDictionary
    checked.physical.binding limits.toLimits (readFrames limits) index

def PageWire (limits : Limits) (source : Bytes) (frame : Page.Frame) (slots : List (Option Bytes)) : Prop :=
  (∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 0) ∧
    Utf8.Fallback.Snappy.PlainBytesWire limits source frame slots

/-- The raw definitions precede the exact original flag-selected value suffix. -/
def SuffixWire (limits : Limits) (source : Bytes) (frame : Page.Frame) (slots : List (Option Bytes)) : Prop :=
  ∃ (header : Page.DataV2) (layout : FlatPage.Layout) (definitions : Bytes) (stored : List UInt8),
    let decoded := Plain.ByteArray.wire (slots.filterMap id)
    frame.value.kind = .dataV2 header ∧ header.encoding = 0 ∧ header.repetitionBytes = 0 ∧
    header.numRows = header.numValues ∧ header.numNulls ≤ header.numValues ∧
    header.definitionBytes ≤ frame.value.compressedSize ∧ header.definitionBytes ≤ frame.value.uncompressedSize ∧
    header.definitionBytes ≤ limits.scalar.levels.bytes ∧ definitions.length = header.definitionBytes ∧
    (Page.Checksum.payloadBytes source frame).toList = definitions.toList ++ stored ∧
    FlatPage.readMask layout header.numValues limits.scalar.levels definitions = .ok (slots.map Option.isSome) ∧
    (slots.map Option.isSome).count true = header.numValues - header.numNulls ∧ slots.length = header.numValues ∧
    stored.length = frame.value.compressedSize - header.definitionBytes ∧
    decoded.length = frame.value.uncompressedSize - header.definitionBytes ∧
    (if header.isCompressed then
      Payload.Decodes (frame.value.uncompressedSize - header.definitionBytes) .snappy stored decoded
     else decoded = stored)

def FramesWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (rows : Nat)
    (frames : List Page.Frame) (slots : List (Option Bytes)) : Prop :=
  Utf8.Dictionary.Snappy.expandedBytes frames ≤ limits.maxExpandedChunkBytes ∧
  (Utf8.Dictionary.Snappy.expandedBytes frames : Int) = metadata.totalUncompressedSize ∧
  metadata.dictionaryPageOffset = none ∧
  frames.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
  ∃ pages, List.Forall₂ (PageWire limits source) frames pages ∧ slots = pages.flatten ∧ slots.length = rows

def GroupWire {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option Bytes)) : Prop :=
  ByteArrayFallback.BoundGroupWireWithCodec .snappy checked.physical.binding limits.toLimits
    (fun metadata source rows frames output =>
      (Utf8.Dictionary.Snappy.storedBytes frames : Int) = metadata.totalCompressedSize ∧
      Utf8.Dictionary.Snappy.storedBytes frames ≤ limits.file.column.maxChunkBytes ∧
      FramesWire limits metadata source rows frames output) index group slots

abbrev schema (name : String) := Plain.ByteArray.File.schema name .optional
abbrev Value := Plain.ByteArray.File.Value

def rowsAt {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat) :
    Except Snappy.GroupError (Reader.RowGroup (schema name) Value) :=
  (readGroup limits checked index).map (Plain.ByteArray.File.rows name .optional)

def source {name : String} (limits : Limits) (checked : Snappy.Checked name) :
    Reader.Source Nat (schema name) Value Snappy.GroupError :=
  ⟨List.range checked.physical.snapshot.groupCount, rowsAt limits checked, fun _ => .ok ()⟩

/-- Observe completed groups and the original termination of the checked source. -/
def readAll {name : String} (limits : Limits) (checked : Snappy.Checked name) :
    Arrow.Events.EventStream String Value Snappy.GroupError :=
  Reader.readAll (.ok ⟨schema name, source limits checked⟩)

/-- Export the selected opaque PLAIN groups through native BinaryView EOS. -/
def convert (parquet : Limits) (ipc : Arrow.Limits) (view : Column.Limits) (input : Bytes)
    (name : String) : Except Snappy.Error KBytes :=
  Snappy.convertWith parquet ipc view input name (readGroup parquet)

end Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2
