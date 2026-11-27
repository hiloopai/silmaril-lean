module

public import Silmaril.Formats.Parquet.Date.Leaf.Zstd.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec

/-! Opt-in selected Zstandard PLAIN DATE data page V2. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2

open Compression.Zstd

abbrev Limits := Zstd.Limits

inductive GroupError where
  | zstd (cause : Zstd.GroupError)
  | expectedV2 (ordinal offset : Nat)
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

/-- Keep the V2 level extents and resolved compression flag on the original frame. -/
def planData (bound : Bound) (frame : Page.Frame) (ordinal : Nat) :
    Except GroupError Gzip.DataPage := do
  let .dataV2 header := frame.value.kind | throw (.expectedV2 ordinal frame.header.start)
  if header.encoding ≠ 0 then
    throw (.zstd (.plan (Gzip.atFrame ordinal frame (.encoding header.encoding))))
  let some params := FlatColumn.pageParameters (Zstd.columnLayout bound) Payload.Codec.zstd.id frame.value |
    throw (.expectedV2 ordinal frame.header.start)
  return ⟨frame, params⟩

def checkGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Gzip.CheckedGroup :=
  Gzip.checkGroupFor .zstd (.zstd ∘ Zstd.GroupError.plan) (planData bound) limits.pages bound index

abbrev GroupWire (limits : Limits) (bound : Bound) (index : Nat) (checked : Gzip.CheckedGroup) :=
  Gzip.GroupWire limits.pages bound index checked (fun page => ∃ i, planData bound page.frame i = .ok page) .zstd

/-- Check the whole stored CRC before splitting raw levels from values. -/
def decodePage (limits : Limits) (bound : Bound) (metadata : Footer.ColumnMetadata)
    (page : Gzip.DataPage) (ordinal : Nat) : Except GroupError Slots :=
  (Zstd.decodePage limits bound metadata page ordinal).mapError .zstd

def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  let checked ← checkGroup limits bound index
  let pages ← checked.data.zipIdx.mapM fun (page, i) =>
    decodePage limits bound checked.selection.column.metadata page i
  return pages.flatten

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Publish complete native Date32 IPC after the checked source reaches EOS. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

def SuffixWire (limits : Limits) (frame : Page.Frame) (data : Page.DataV2)
    (stored plain : List UInt8) : Prop :=
  stored.length = frame.value.compressedSize - data.definitionBytes ∧
  plain.length = frame.value.uncompressedSize - data.definitionBytes ∧
  if data.isCompressed then
    ∃ header, CheckedFrame.Huffman.FrameWire
      (FlatColumn.Zstd.frameLimits limits.compression (limits.pages.scalar.payloadBounds
        ⟨frame.value.compressedSize, frame.value.uncompressedSize⟩ data.definitionBytes))
      stored plain header ∧ header.windowSize ≤ limits.compression.window
  else plain = stored

/-- The original stored prefix supplies the definition mask. Only the suffix
goes through the original header's flag-selected scalar decoding path. -/
structure PageWire (limits : Limits) (source : Bytes) (page : Gzip.DataPage) (slots : Slots) : Prop where
  count : slots.length = page.params.numValues
  original : let frame := page.frame
    let stored := Page.Checksum.payloadBytes source frame
    ∃ (status : Page.Checksum.Status), ∃ data layout definitions encoded,
      ∃ (prepared : ScalarPage.Prepared), ∃ words,
      frame.value.kind = .dataV2 data ∧ data.encoding = 0 ∧
      source.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.pages.scalar.compressedBytes ∧
      frame.value.uncompressedSize ≤ limits.pages.scalar.uncompressedBytes ∧
      (match status with
       | Page.Checksum.Status.absent => frame.value.crc = none
       | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
      data.numRows = data.numValues ∧ data.numNulls ≤ data.numValues ∧
      data.repetitionBytes = 0 ∧ data.definitionBytes ≤ frame.value.compressedSize ∧
      data.definitionBytes ≤ frame.value.uncompressedSize ∧
      data.definitionBytes ≤ limits.pages.scalar.levels.bytes ∧
      definitions.length = data.definitionBytes ∧ stored.toList = definitions.toList ++ encoded ∧
      SuffixWire limits frame data encoded prepared.scalars.toList ∧
      ScalarPage.validate page.params limits.pages.scalar stored = .ok layout ∧
      FlatPage.readMask layout data.numValues limits.pages.scalar.levels definitions = .ok prepared.mask ∧
      Plain.decodeInt32 (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words ∧
      slots.length = data.numValues ∧ (slots.filterMap id).length + data.numNulls = data.numValues

end Silmaril.Formats.Parquet.Date.Leaf.Zstd.V2
