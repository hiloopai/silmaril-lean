module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec

/-! Selected modern TIMESTAMP with codec-0 or Snappy DELTA_BINARY_PACKED V1/V2 data. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Delta

def defaultLimits : DeltaBinaryPacked.Limits :=
  ⟨16 * 1024 * 1024, 1024 * 1024, 4096, 128, 1024 * 1024⟩

def decoderLimits (page : ScalarPage.Limits) (packed : DeltaBinaryPacked.Limits) : DeltaPage.Limits :=
  -- The INT64 path never uses the byte-array decoders.
  let inactive : DeltaLengthByteArray.Limits := ⟨packed, 0, 0⟩
  ⟨page, packed, inactive, ⟨packed, inactive, 0, 0⟩⟩

structure CheckedGroup where
  chunk : Leaf.Chunk
  frames : List Parquet.Page.Frame

/-- Select the original dictionary-free chunk and check its framed row total. -/
def checkGroup (limits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error CheckedGroup := do
  let chunk ← Leaf.selectChunkWith .deltaBinaryPacked limits bound index
  let frames ← (Parquet.Page.readChunk limits.framing bound.snapshot.bytes chunk.span).mapError .framing
  let expected := chunk.group.numRows.toNat
  let actual := (frames.map Internal.pageSlots).sum
  if actual ≠ expected then throw (.rowCount expected actual)
  return ⟨chunk, frames⟩

/-- Verify the stored extent and any CRC before decoding the original tag-5 body. -/
def decodePage (packed : DeltaBinaryPacked.Limits) (limits : ScalarPage.Limits) (bound : Bound)
    (codec : Int) (frame : Parquet.Page.Frame) (ordinal : Nat) : Except Leaf.Error (List (Option Int64)) := do
  let _ ← (Parquet.Page.Checksum.verify limits.compressedBytes bound.snapshot.bytes frame).mapError
    (.pageChecksum ordinal frame.header.start)
  let atPage := Leaf.Error.deltaPage ordinal frame.header.start
  let params ← (Timestamp.Page.parameters bound.binding.leaf bound.levels codec frame.value).mapError
    (atPage ∘ .parameters)
  (DeltaPage.decode (.signed .int64) params (decoderLimits limits packed) (Internal.body bound frame)).mapError
    (atPage ∘ .decode)

/-- The original stored page, exact prepared layout, bounded delta stream,
and ordered nullable signed output. -/
def PageWire (packed : DeltaBinaryPacked.Limits) (limits : ScalarPage.Limits) (bound : Bound)
    (codec : Int) (frame : Parquet.Page.Frame) (slots : List (Option Int64)) : Prop :=
  let stored := Internal.body bound frame
  ∃ status params layout prepared, ∃ stream : DeltaBinaryPacked.Stream,
    Parquet.Page.Checksum.verify limits.compressedBytes bound.snapshot.bytes frame = .ok status ∧
    bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.compressedBytes ∧
    (match status with
      | .absent => frame.value.crc = none
      | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
    Timestamp.Page.parameters bound.binding.leaf bound.levels codec frame.value = .ok params ∧
    params.encoding = 5 ∧
    ScalarPage.validateFor 5 params limits stored = .ok layout ∧
    ScalarPage.PreparedWire params limits layout stored prepared ∧
    prepared.scalars.length ≤ packed.bytes ∧ prepared.scalars.toList = stream.wire ∧
    stream.Valid .int64 packed (prepared.mask.count true) ∧
    slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = stream.reconstruct .int64 ∧
    slots.length = Internal.pageSlots frame ∧
    (slots.filterMap id).length = prepared.mask.count true

def readGroup (packed : DeltaBinaryPacked.Limits) (limits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error (Slots bound) := do
  let group ← checkGroup limits bound index
  let codec := group.chunk.column.metadata.codec
  let pages ← group.frames.zipIdx.mapM fun (frame, ordinal) => decodePage packed limits.page bound codec frame ordinal
  return pages.flatten.map (Option.map bound.binding.descriptor.decode)

def readBound (packed : DeltaBinaryPacked.Limits) (limits : Leaf.Limits) (bound : Bound) : Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup packed limits bound)

/-- Opt into dictionary-free DELTA_BINARY_PACKED on one modern flat INT64 leaf. -/
def convert (packed : DeltaBinaryPacked.Limits) (inputLimits : Events.ToIpc.Limits)
    (outputLimits : Arrow.ObservationLimits) (input : Bytes) (ordinal : Nat) :
    Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal (readGroup packed inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Delta
