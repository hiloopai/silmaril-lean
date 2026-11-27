module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Defs
public import Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2.Defs

/-! Opt-in selected Zstandard DATE with one PLAIN dictionary and only
RLE_DICTIONARY V2 data pages. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2

open Compression.Zstd
open DictionaryChunk (DataPage)

structure Limits extends toChunkLimits : Snappy.Limits where
  compression : FlatColumn.Zstd.CompressionLimits := ⟨8 * 1024 * 1024, 43690⟩

abbrev CheckedGroup := Snappy.CheckedGroup

def scalarLimits (limits : Limits) : Leaf.Zstd.Limits :=
  ⟨⟨limits.page, limits.scalar, limits.maxRows, limits.maxChunkBytes, limits.maxExpandedChunkBytes⟩,
    limits.compression⟩

inductive DictionaryError where
  | expectedDictionary
  | encoding (actual : Int)
  | entryLimit
  | checksum (cause : Page.Checksum.Error)
  | payload (cause : FlatColumn.Zstd.Error)
  | entries (cause : Plain.Error)
  deriving DecidableEq, Repr

inductive HeaderError where
  | expectedV2
  | encoding (actual : Int)
  deriving DecidableEq, Repr

inductive GroupError where
  | chunk (cause : Snappy.GroupError)
  | dictionary (offset : Nat) (cause : DictionaryError)
  | header (page offset : Nat) (cause : HeaderError)
  | preparation (page offset : Nat) (cause : FlatColumn.Zstd.Error)
  deriving DecidableEq, Repr

inductive Error where
  | openFailure (cause : Leaf.Error)
  | groupFailure (index : Nat) (cause : GroupError)
  deriving DecidableEq, Repr

inductive IpcError where
  | source (cause : Error)
  | closed
  | writer (cause : Arrow.DateStream.Writer.Error)
  deriving DecidableEq, Repr

/-- The leading dictionary uses one whole-body Zstandard frame. -/
def readEntries (limits : Limits) (source : Bytes) (frame : Page.Frame) :
    Except DictionaryError (List Int32) := do
  let .dictionary header := frame.value.kind | throw .expectedDictionary
  if header.encoding ≠ 0 then throw (.encoding header.encoding)
  if limits.maxEntries < header.numValues then throw .entryLimit
  let bounds := Snappy.dictionaryBounds limits.toChunkLimits frame
  let _ ← (Page.Checksum.verify bounds.compressedLimit source frame).mapError .checksum
  let expanded ← (FlatColumn.Zstd.decodePayload limits.compression bounds Payload.Codec.zstd.id
    (Page.Checksum.payloadBytes source frame).toList).mapError .payload
  (Plain.decodeInt32 header.numValues (Bytes.ofList expanded)).mapError .entries

/-- Select tag 8 on an original Data Page V2 header. -/
def planData (bound : Bound) (frame : Page.Frame) : Except HeaderError DataPage := do
  let .dataV2 header := frame.value.kind | throw .expectedV2
  if header.encoding ≠ 8 then throw (.encoding header.encoding)
  let some params := FlatColumn.pageParameters (Leaf.Zstd.columnLayout bound) Payload.Codec.zstd.id frame.value |
    throw .expectedV2
  return ⟨frame, params⟩

def planPages (bound : Bound) (frames : List Page.Frame) : Except GroupError (List DataPage) :=
  (frames.zipIdx 1).mapM fun (frame, i) => (planData bound frame).mapError (.header i frame.header.start)

def checkGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError CheckedGroup :=
  Snappy.checkGroupWithDictionary .zstd .chunk (fun frame => .dictionary frame.header.start)
    (readEntries limits) (planPages bound) limits.toChunkLimits bound index

abbrev GroupWire (limits : Limits) (bound : Bound) (index : Nat) (checked : CheckedGroup) :=
  Snappy.GroupWireWith limits.toChunkLimits bound index checked .zstd (readEntries limits)
    (fun page => planData bound page.frame = .ok page)

def decodeReferences (limits : Hybrid.Limits) (entries : Array Int32) (page : ScalarPage.Prepared) :
    Except DictionaryIndex.Error Slots := do
  let indices ← DictionaryIndex.readIndices limits (page.mask.count true) page.scalars
  let values ← DictionaryIndex.select entries indices
  (FlatPage.reconstruct page.mask values).mapError .slots

/-- Verify the whole stored CRC before reading the raw V2 levels or references. -/
def decodePage (limits : Limits) (source : Bytes) (entries : Array Int32)
    (page : DataPage) (ordinal : Nat) : Except GroupError Slots := do
  let _ ← (Snappy.verifyData limits.toChunkLimits source page ordinal).mapError .chunk
  let prepared ← (FlatColumn.Zstd.prepareFor 8 (Leaf.Zstd.columnLimits (scalarLimits limits)) page.params
    (Page.Checksum.payloadBytes source page.frame)).mapError (.preparation ordinal page.frame.header.start)
  (decodeReferences limits.indices entries prepared).mapError (GroupError.chunk ∘
    Snappy.atFrame ordinal page.frame ∘ Snappy.PageError.references)

def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots :=
  Fallback.Gzip.readGroupWith (checkGroup limits bound) (decodePage limits) bound index

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Emit native Date32 IPC after the original source reaches EOS. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

def DictionaryWire (limits : Limits) (source : Bytes) (frame : Page.Frame) (entries : List Int32) : Prop :=
  let stored := Page.Checksum.payloadBytes source frame
  let bounds := Snappy.dictionaryBounds limits.toChunkLimits frame
  ∃ (status : Page.Checksum.Status), ∃ data expanded header,
    frame.value.kind = .dictionary data ∧ data.encoding = 0 ∧ data.numValues ≤ limits.maxEntries ∧
    source.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ bounds.compressedLimit ∧
    (match status with
     | .absent => frame.value.crc = none
     | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
    CheckedFrame.Huffman.FrameWire (FlatColumn.Zstd.frameLimits limits.compression bounds)
      stored.toList expanded header ∧ header.windowSize ≤ limits.compression.window ∧
    expanded.length = frame.value.uncompressedSize ∧ expanded.length ≤ bounds.outputLimit ∧
    Plain.decodeInt32 data.numValues (Bytes.ofList expanded) = .ok entries ∧ entries.length = data.numValues

/-- An admitted page consumes the original raw levels and flag-selected
reference stream and looks up each original index in wire order. -/
structure PageWire (limits : Limits) (source : Bytes) (entries : Array Int32) (page : DataPage)
    (slots : Slots) : Prop where
  count : slots.length = page.params.numValues
  wire : let frame := page.frame
    let stored := Page.Checksum.payloadBytes source frame
    ∃ (status : Page.Checksum.Status), ∃ data layout definitions encoded,
      ∃ (prepared : ScalarPage.Prepared), ∃ width runs indices,
      frame.value.kind = .dataV2 data ∧ data.encoding = 8 ∧
      source.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.scalar.compressedBytes ∧
      frame.value.uncompressedSize ≤ limits.scalar.uncompressedBytes ∧
      (match status with
       | .absent => frame.value.crc = none
       | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
      data.numRows = data.numValues ∧ data.numNulls ≤ data.numValues ∧
      data.repetitionBytes = 0 ∧ data.definitionBytes ≤ frame.value.compressedSize ∧
      data.definitionBytes ≤ frame.value.uncompressedSize ∧ data.definitionBytes ≤ limits.scalar.levels.bytes ∧
      definitions.length = data.definitionBytes ∧ stored.toList = definitions.toList ++ encoded ∧
      Leaf.Zstd.V2.SuffixWire (scalarLimits limits) frame data encoded prepared.scalars.toList ∧
      ScalarPage.validateFor 8 page.params limits.scalar stored = .ok layout ∧
      FlatPage.readMask layout data.numValues limits.scalar.levels definitions = .ok prepared.mask ∧
      prepared.scalars.toList = width :: runs ∧ width.toNat ≤ 32 ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      indices.map (fun i => entries[i]?) = (slots.filterMap id).map some ∧
      slots.map Option.isSome = prepared.mask ∧
      slots.length = data.numValues ∧ (slots.filterMap id).length + data.numNulls = data.numValues

end Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2
