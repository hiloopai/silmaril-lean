module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs
public import Silmaril.Formats.Parquet.FlatColumn.Zstd.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec

/-! Strict selected PLAIN V2 TIMESTAMP with a checked Zstandard value suffix. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2

open Silmaril.Relational

structure Limits where
  maxStoredChunkBytes : Nat := 64 * 1024 * 1024
  maxExpandedChunkBytes : Nat := 64 * 1024 * 1024
  compression : FlatColumn.Zstd.CompressionLimits := ⟨8 * 1024 * 1024, 43690⟩

inductive GroupError where
  | selection (cause : Leaf.Error)
  | expandedChunkLimit
  | expectedV2 (ordinal offset : Nat)
  | parameters (ordinal offset : Nat) (cause : Timestamp.Page.Error)
  | checksum (ordinal offset : Nat) (cause : Parquet.Page.Checksum.Error)
  | decode (ordinal offset : Nat) (cause : FlatColumn.Zstd.Error)
  | references (ordinal offset : Nat) (cause : DictionaryIndex.Error)
  deriving DecidableEq, Repr

inductive SourceError where
  | groupFailure (index : Nat) (cause : GroupError)
  deriving DecidableEq, Repr

inductive Error where
  | openFailure (cause : Events.ToIpc.Error)
  | source (cause : SourceError)
  | closed
  | fieldCount (actual : Nat)
  | writer (cause : Arrow.TimestampStream.Writer.Error)
  deriving DecidableEq, Repr

structure CheckedGroup where
  chunk : Leaf.Chunk
  frames : List Parquet.Page.Frame

def columnLimits (limits : Limits) (leafLimits : Leaf.Limits) : FlatColumn.Zstd.Limits :=
  ⟨⟨leafLimits.framing, limits.maxStoredChunkBytes, leafLimits.page.compressedBytes, leafLimits.maxRows⟩,
    leafLimits.page, limits.compression⟩

/-- The selected original span and the total declared expansion and row count
are bounded before any value suffix is decoded. -/
def checkGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError CheckedGroup := do
  let chunk ← (selectChunkWith .zstdPlainV2 leafLimits bound index).mapError .selection
  if limits.maxStoredChunkBytes < chunk.span.stop - chunk.span.start then
    throw (.selection .chunkByteLimit)
  let frames ← (Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes chunk.span).mapError
    (.selection ∘ .framing)
  if limits.maxExpandedChunkBytes < (frames.map (·.value.uncompressedSize)).sum then
    throw .expandedChunkLimit
  let expected := chunk.group.numRows.toNat
  let actual := (frames.map Internal.pageSlots).sum
  if actual ≠ expected then throw (.selection (.rowCount expected actual))
  return ⟨chunk, frames⟩

def decodeBody (limits : FlatColumn.Zstd.Limits) (params : ScalarPage.Parameters) (body : Bytes) :
    Except FlatColumn.Zstd.Error (List (Option Int64)) := do
  let prepared ← FlatColumn.Zstd.prepareFor 0 limits params body
  let words ← (Plain.decodeInt64 (prepared.mask.count true) prepared.scalars).mapError (.scalar ∘ .plain)
  (FlatPage.reconstruct prepared.mask words).mapError (.scalar ∘ .levels)

/-- Check the CRC against the complete original body, then let the V2
parameters select the exact raw or Zstandard suffix. -/
def decodePage (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (frame : Parquet.Page.Frame)
    (ordinal : Nat) : Except GroupError (List (Option Int64)) := do
  let .dataV2 _ := frame.value.kind | throw (.expectedV2 ordinal frame.header.start)
  let _ ← (Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes frame).mapError
    (.checksum ordinal frame.header.start)
  let params ← (Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.zstd.id frame.value).mapError
    (.parameters ordinal frame.header.start)
  (decodeBody (columnLimits limits leafLimits) params
    (Internal.body bound frame)).mapError (.decode ordinal frame.header.start)

def SuffixWire (limits : Limits) (leafLimits : Leaf.Limits) (frame : Parquet.Page.Frame)
    (header : Parquet.Page.DataV2) (stored plain : List UInt8) : Prop :=
  stored.length = frame.value.compressedSize - header.definitionBytes ∧
  plain.length = frame.value.uncompressedSize - header.definitionBytes ∧
  if header.isCompressed then
    ∃ parsed, Compression.Zstd.CheckedFrame.Huffman.FrameWire
      (FlatColumn.Zstd.frameLimits limits.compression (leafLimits.page.payloadBounds
        ⟨frame.value.compressedSize, frame.value.uncompressedSize⟩ header.definitionBytes))
      stored plain parsed ∧ parsed.windowSize ≤ limits.compression.window
  else plain = stored

/-- The original CRC-covered body splits into raw definitions and exactly
the literal or checked frame suffix selected by the V2 flag. -/
structure PageWire (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (frame : Parquet.Page.Frame) (slots : List (Option Int64)) : Prop where
  count : slots.length = Internal.pageSlots frame
  original : let body := Internal.body bound frame
    ∃ status header layout definitions encoded, ∃ prepared : ScalarPage.Prepared, ∃ words,
      frame.value.kind = .dataV2 header ∧ header.encoding = 0 ∧
      bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some body ∧
      body.length = frame.value.compressedSize ∧ frame.value.compressedSize ≤ leafLimits.page.compressedBytes ∧
      frame.value.uncompressedSize ≤ leafLimits.page.uncompressedBytes ∧
      (match status with
       | Parquet.Page.Checksum.Status.absent => frame.value.crc = none
       | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec body.toList = crc) ∧
      header.numRows = header.numValues ∧ header.numNulls ≤ header.numValues ∧
      header.repetitionBytes = 0 ∧ header.definitionBytes ≤ frame.value.compressedSize ∧
      header.definitionBytes ≤ frame.value.uncompressedSize ∧ header.definitionBytes ≤ leafLimits.page.levels.bytes ∧
      definitions.length = header.definitionBytes ∧ body.toList = definitions.toList ++ encoded ∧
      SuffixWire limits leafLimits frame header encoded prepared.scalars.toList ∧
      FlatPage.readMask layout header.numValues leafLimits.page.levels definitions = .ok prepared.mask ∧
      Plain.decodeInt64 (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words ∧
      (slots.filterMap id).length + header.numNulls = header.numValues

def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError (Slots bound) := do
  let checked ← checkGroup limits leafLimits bound index
  let pages ← checked.frames.zipIdx.mapM fun (frame, ordinal) =>
    decodePage limits leafLimits bound frame ordinal
  return pages.flatten.map (Option.map bound.binding.descriptor.decode)

def rowsAtWith (bound : Bound) (read : Nat → Except GroupError (Slots bound)) (index : Nat) :
    Except SourceError (Reader.RowGroup (Events.schema bound) Events.Cell) :=
  (read index).map (Events.rows bound) |>.mapError (.groupFailure index)

def rowsAt (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :=
  rowsAtWith bound (readGroup limits leafLimits bound)

abbrev Source := Arrow.Events.EventStream String Events.Cell SourceError

def readBoundWith (bound : Bound) (read : Nat → Except GroupError (Slots bound)) : Source :=
  Reader.readAll (.ok ⟨Events.schema bound, ⟨List.range bound.snapshot.groupCount,
    rowsAtWith bound read, fun _ => .ok ()⟩⟩)

def readBound (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) : Source :=
  readBoundWith bound (readGroup limits leafLimits bound)

def emit (output : Arrow.ObservationLimits) (source : Source) : Except Error KBytes :=
  match source with
  | .error cause => .error (.source cause)
  | .ok ⟨schema, trace⟩ =>
    match trace.termination with
    | .readError cause | .closeError cause => .error (.source cause)
    | .closed => .error .closed
    | .eos =>
      if one : schema.width = 1 then
        let column : Fin schema.width := ⟨0, by omega⟩
        let binding := Events.ToIpc.bindingAt schema column
        (Arrow.TimestampStream.Writer.emit output binding
          (trace.batches.map fun batch => batch.values column)).mapError .writer
      else .error (.fieldCount schema.width)

def convertWith (inputLimits : Events.ToIpc.Limits) (output : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) (read : (bound : Bound) → Nat → Except GroupError (Slots bound)) :
    Except Error KBytes := do
  let bound ← (Events.ToIpc.openBound inputLimits input ordinal).mapError .openFailure
  emit output (readBoundWith bound (read bound))

/-- Retain the original codec error until complete source EOS and native IPC emission. -/
def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (output : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Error KBytes :=
  convertWith inputLimits output input ordinal (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2
