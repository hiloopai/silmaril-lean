module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec

/-! Selected modern TIMESTAMP with UNCOMPRESSED or Snappy BYTE_STREAM_SPLIT V1/V2 data. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.ByteStreamSplit

def defaultLimits : Parquet.ByteStreamSplit.Limits :=
  ⟨1024 * 1024, 8 * 1024 * 1024, 8⟩

structure CheckedGroup where
  chunk : Leaf.Chunk
  frames : List Parquet.Page.Frame

/-- Select the original dictionary-free chunk and check its framed row total. -/
def checkGroup (limits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error CheckedGroup := do
  let chunk ← Leaf.selectChunkWith .byteStreamSplit limits bound index
  let frames ← (Parquet.Page.readChunk limits.framing bound.snapshot.bytes chunk.span).mapError .framing
  let expected := chunk.group.numRows.toNat
  let actual := (frames.map Internal.pageSlots).sum
  if actual ≠ expected then throw (.rowCount expected actual)
  return ⟨chunk, frames⟩

/-- Verify the original stored extent and any CRC before decoding the tag-9 page. -/
def decodePage (scalars : Parquet.ByteStreamSplit.Limits) (limits : ScalarPage.Limits) (bound : Bound)
    (codec : Int) (frame : Parquet.Page.Frame) (ordinal : Nat) : Except Leaf.Error (List (Option Int64)) := do
  let _ ← (Parquet.Page.Checksum.verify limits.compressedBytes bound.snapshot.bytes frame).mapError
    (.pageChecksum ordinal frame.header.start)
  let atPage := Leaf.Error.byteStreamSplitPage ordinal frame.header.start
  let params ← (Timestamp.Page.parameters bound.binding.leaf bound.levels codec frame.value).mapError
    (atPage ∘ .parameters)
  let decoded ← (ByteStreamSplitPage.decode bound.binding.leaf .int64 params ⟨limits, scalars⟩
    (Internal.body bound frame)).mapError (atPage ∘ .decode)
  match decoded with
  | ⟨.int64, slots⟩ => pure slots
  | _ => throw (atPage .physicalKind)

/-- Original stored extent and checksum, exact prepared level/value layout, and
the eight lanes from which each present signed little-endian word is read. -/
def PageWire (scalars : Parquet.ByteStreamSplit.Limits) (limits : ScalarPage.Limits) (bound : Bound)
    (codec : Int) (frame : Parquet.Page.Frame) (slots : List (Option Int64)) : Prop :=
  let stored := Internal.body bound frame
  ∃ status params layout prepared words,
    Parquet.Page.Checksum.verify limits.compressedBytes bound.snapshot.bytes frame = .ok status ∧
    bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.compressedBytes ∧
    (match status with
      | .absent => frame.value.crc = none
      | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
    Timestamp.Page.parameters bound.binding.leaf bound.levels codec frame.value = .ok params ∧
    params.encoding = 9 ∧
    ScalarPage.validateFor 9 params limits stored = .ok layout ∧
    ScalarPage.PreparedWire params limits layout stored prepared ∧
    Parquet.ByteStreamSplit.Admission scalars 8 (prepared.mask.count true) prepared.scalars ∧
    Parquet.ByteStreamSplit.LaneOrder 8 (prepared.mask.count true) prepared.scalars words ∧
    slots.map Option.isSome = prepared.mask ∧
    slots.filterMap id = words.map (fun word => (Plain.readUInt64Word word).toInt64) ∧
    slots.length = Internal.pageSlots frame ∧
    (slots.filterMap id).length = prepared.mask.count true

def readGroup (scalars : Parquet.ByteStreamSplit.Limits) (limits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error (Slots bound) := do
  let group ← checkGroup limits bound index
  let codec := group.chunk.column.metadata.codec
  let pages ← group.frames.zipIdx.mapM fun (frame, ordinal) => decodePage scalars limits.page bound codec frame ordinal
  return pages.flatten.map (Option.map bound.binding.descriptor.decode)

def readBound (scalars : Parquet.ByteStreamSplit.Limits) (limits : Leaf.Limits) (bound : Bound) : Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup scalars limits bound)

/-- Opt into dictionary-free BYTE_STREAM_SPLIT on one modern flat INT64 leaf. -/
def convert (scalars : Parquet.ByteStreamSplit.Limits) (inputLimits : Events.ToIpc.Limits)
    (outputLimits : Arrow.ObservationLimits) (input : Bytes) (ordinal : Nat) :
    Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal (readGroup scalars inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.ByteStreamSplit
