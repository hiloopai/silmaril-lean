module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Defs
public import Silmaril.Formats.Parquet.FlatColumn.Zstd.Defs

/-! Opt-in Zstandard PLAIN V2 over one flat optional unannotated BYTE_ARRAY. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2

open Arrow.BinaryView
open Silmaril.Formats.Parquet.Plain.ByteArray

structure Limits where
  file : File.Limits := {}
  maxExpandedPageBytes : Nat := 16 * 1024 * 1024
  maxExpandedChunkBytes : Nat := 64 * 1024 * 1024
  compression : FlatColumn.Zstd.CompressionLimits := ⟨8 * 1024 * 1024, 43690⟩

def Limits.physical (limits : Limits) : Snappy.Limits :=
  { file := limits.file, maxExpandedPageBytes := limits.maxExpandedPageBytes,
    maxExpandedChunkBytes := limits.maxExpandedChunkBytes }

def Limits.page (limits : Limits) : FlatColumn.Zstd.Limits :=
  ⟨limits.file.column, limits.physical.scalar, limits.compression⟩

inductive DecodeError where
  | unadvertisedPlain
  | zstd (cause : FlatColumn.Zstd.Error)
  deriving DecidableEq, Repr

abbrev GroupError := FlatColumn.Error DecodeError

inductive Error where
  | openFile (cause : Snappy.OpenError)
  | column (cause : GroupError)
  | writer (cause : StreamWriter.Error)
  deriving DecidableEq, Repr

/-- Verify the complete original stored body before preparing levels and values. -/
def decodePage (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (frame : Page.Frame) : Except (FlatColumn.PageError DecodeError) (List (Option Bytes)) := do
  match frame.value.kind with
  | .dataV2 data =>
    if data.encoding ≠ 0 then throw (.encoding data.encoding)
    if !metadata.encodings.contains 0 then throw (.decode .unadvertisedPlain)
    let _ ← (Page.Checksum.verify limits.file.column.maxPageBytes source frame).mapError .checksum
    let some params := FlatColumn.pageParameters .optional Payload.Codec.zstd.id frame.value |
      throw .unsupportedKind
    let prepared ← (FlatColumn.Zstd.prepareFor 0 limits.page params (Page.Checksum.payloadBytes source frame))
      |>.mapError (.decode ∘ .zstd)
    let values ← (Plain.ByteArray.decode (Utf8.Fallback.Snappy.plainLimits limits.physical)
      (prepared.mask.count true) prepared.scalars).mapError (.decode ∘ .zstd ∘ .scalar ∘ .plain)
    (FlatPage.reconstruct prepared.mask values).mapError (.decode ∘ .zstd ∘ .scalar ∘ .levels)
  | .dataV1 _ => throw .unsupportedVersion
  | .dictionary _ | .skipped _ => throw .unsupportedKind

def rejectDictionary (_ : Page.Frame) : Except (FlatColumn.PageError DecodeError) Unit :=
  .error .unsupportedKind

def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except GroupError (List (Option Bytes)) := do
  Utf8.Dictionary.Snappy.checkExpandedChunk limits.physical metadata group column name frames
  ByteArrayFallback.readFramesWith rejectDictionary (fun _ => decodePage limits metadata source)
    metadata group column name rows frames

def readGroup {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat) :
    Except GroupError (List (Option Bytes)) :=
  ByteArrayFallback.readBoundGroupWithCodec .zstd limits.maxExpandedChunkBytes .rleDictionary
    checked.physical.binding limits.physical.toLimits (readFrames limits) index

/-- The original raw levels and flag-selected suffix account for every opaque slot. -/
def PageWire (limits : Limits) (source : Bytes) (frame : Page.Frame) (slots : List (Option Bytes)) : Prop :=
  Utf8.Dictionary.Snappy.StoredWire limits.file.column.maxPageBytes source frame ∧
  frame.value.uncompressedSize ≤ limits.maxExpandedPageBytes ∧
  ∃ (data : Page.DataV2) (layout : FlatPage.Layout) (definitions : Bytes) (encoded : List UInt8),
    frame.value.kind = .dataV2 data ∧ data.encoding = 0 ∧ data.repetitionBytes = 0 ∧
    data.numRows = data.numValues ∧ data.numNulls ≤ data.numValues ∧
    data.definitionBytes ≤ frame.value.compressedSize ∧ data.definitionBytes ≤ frame.value.uncompressedSize ∧
    data.definitionBytes ≤ limits.page.scalar.levels.bytes ∧ definitions.length = data.definitionBytes ∧
    (Page.Checksum.payloadBytes source frame).toList = definitions.toList ++ encoded ∧
    FlatPage.readMask layout data.numValues limits.page.scalar.levels definitions = .ok (slots.map Option.isSome) ∧
    (slots.map Option.isSome).count true = data.numValues - data.numNulls ∧
    slots.length = data.numValues ∧
    FlatColumn.Zstd.PayloadWire limits.compression
      (limits.page.scalar.payloadBounds ⟨frame.value.compressedSize, frame.value.uncompressedSize⟩ data.definitionBytes)
      (ScalarPage.v2Codec Payload.Codec.zstd.id (some data.isCompressed)) encoded
      (Plain.ByteArray.wire (slots.filterMap id))

def FramesWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (rows : Nat)
    (frames : List Page.Frame) (slots : List (Option Bytes)) : Prop :=
  Utf8.Dictionary.Snappy.expandedBytes frames ≤ limits.maxExpandedChunkBytes ∧
  (Utf8.Dictionary.Snappy.expandedBytes frames : Int) = metadata.totalUncompressedSize ∧
  metadata.dictionaryPageOffset = none ∧
  frames.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
  ∃ pages, List.Forall₂ (PageWire limits source) frames pages ∧ slots = pages.flatten ∧ slots.length = rows

def GroupWire {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option Bytes)) : Prop :=
  ByteArrayFallback.BoundGroupWireWithCodec .zstd checked.physical.binding limits.physical.toLimits
    (fun metadata source rows frames output =>
      (Utf8.Dictionary.Snappy.storedBytes frames : Int) = metadata.totalCompressedSize ∧
      Utf8.Dictionary.Snappy.storedBytes frames ≤ limits.file.column.maxChunkBytes ∧
      FramesWire limits metadata source rows frames output) index group slots

/-- Emit native BinaryView only after all selected groups have succeeded. -/
def convert (parquet : Limits) (ipc : Arrow.Limits) (view : Column.Limits) (input : Bytes)
    (name : String) : Except Error KBytes := do
  let checked ← (Snappy.openFile parquet.physical input name).mapError .openFile
  let groups ← ((List.range checked.physical.snapshot.groupCount).mapM (readGroup parquet checked)).mapError .column
  let source : ToIpc.Source := ⟨⟨name, true⟩, groups⟩
  (StreamWriter.emit ipc view source.ipcField source.batches).mapError .writer

end Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2
