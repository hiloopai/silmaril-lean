module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs

/-! Checksummed Snappy PLAIN V2 from the original checked TIMESTAMP leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2

structure CheckedGroup where
  chunk : Leaf.Chunk
  frames : List Parquet.Page.Frame

/-- Require codec 1 and validate the complete framed slot total before decoding. -/
def checkGroup (limits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error CheckedGroup := do
  let chunk ← Leaf.selectChunk {limits with allowSnappy := true} bound index
  if chunk.column.metadata.codec ≠ Payload.Codec.snappy.id then
    Except.error (.chunkCodec chunk.column.metadata.codec)
  let frames ← (Parquet.Page.readChunk limits.framing bound.snapshot.bytes chunk.span).mapError .framing
  let expected := chunk.group.numRows.toNat
  let actual := (frames.map Internal.pageSlots).sum
  if actual ≠ expected then Except.error (.rowCount expected actual)
  return ⟨chunk, frames⟩

/-- Check the exact original stored V2 payload before splitting its raw level
prefix and decoding its potentially compressed value suffix. -/
def decodePage (limits : ScalarPage.Limits) (bound : Bound) (frame : Parquet.Page.Frame)
    (ordinal : Nat) : Except Leaf.Error (List (Option Int64)) := do
  let .dataV2 _ := frame.value.kind | Except.error (.page ordinal .unsupportedPage)
  let _ ← (Parquet.Page.Checksum.verify limits.compressedBytes bound.snapshot.bytes frame).mapError
    (.pageChecksum ordinal frame.header.start)
  let params ← (Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.snappy.id
    frame.value).mapError (.page ordinal)
  (ScalarPage.decode .int64 params limits (Internal.body bound frame)).mapError
    (.page ordinal ∘ .scalar)

def PageWire (limits : ScalarPage.Limits) (bound : Bound) (frame : Parquet.Page.Frame)
    (slots : List (Option Int64)) : Prop :=
  ∃ header status params,
    frame.value.kind = .dataV2 header ∧
      Parquet.Page.Checksum.verify limits.compressedBytes bound.snapshot.bytes frame = .ok status ∧
      Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.snappy.id frame.value =
        .ok params ∧
      ScalarPage.decode .int64 params limits (Internal.body bound frame) = .ok slots ∧
      slots.length = header.numValues

def readGroup (limits : Leaf.Limits) (bound : Bound) (index : Nat) : Except Leaf.Error (Slots bound) := do
  let group ← checkGroup limits bound index
  let slots ← group.frames.zipIdx.mapM fun (frame, ordinal) => decodePage limits.page bound frame ordinal
  return slots.flatten.map (Option.map bound.binding.descriptor.decode)

def readBound (limits : Leaf.Limits) (bound : Bound) : Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits bound)

/-- Opt in to codec-1 PLAIN V2 with stored CRC verification at the selected
TIMESTAMP leaf. Use the strict modern annotation policy. -/
def convert (inputLimits : Events.ToIpc.Limits) (outputLimits : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal
    (readGroup inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2
