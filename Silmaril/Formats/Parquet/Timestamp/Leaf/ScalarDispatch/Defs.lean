module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Delta.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.ByteStreamSplit.Defs

/-! Dictionary-free mixed scalar data pages on one selected INT64 TIMESTAMP leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch

structure Limits where
  delta : DeltaBinaryPacked.Limits := Delta.defaultLimits
  split : Parquet.ByteStreamSplit.Limits := ByteStreamSplit.defaultLimits

inductive Encoding where
  | plain | delta | split
  deriving DecidableEq, Repr

def Encoding.tag : Encoding → Int
  | .plain => 0
  | .delta => 5
  | .split => 9

def Encoding.ofTag (tag : Int) : Option Encoding :=
  if tag = 0 then some .plain
  else if tag = 5 then some .delta
  else if tag = 9 then some .split
  else none

def pageTag (frame : Parquet.Page.Frame) : Option Int :=
  match frame.value.kind with
  | .dataV1 header => some header.encoding
  | .dataV2 header => some header.encoding
  | _ => none

structure CheckedGroup where
  chunk : Leaf.Chunk
  frames : List Parquet.Page.Frame

def checkGroup (limits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error CheckedGroup := do
  let chunk ← Leaf.selectChunkWith .scalarDispatch limits bound index
  let frames ← (Parquet.Page.readChunk limits.framing bound.snapshot.bytes chunk.span).mapError .framing
  let expected := chunk.group.numRows.toNat
  let actual := (frames.map Internal.pageSlots).sum
  if actual ≠ expected then throw (.rowCount expected actual)
  return ⟨chunk, frames⟩

/-- Select a single decoder from the original data header and selected footer declaration. -/
def route (declared : List Int) (frame : Parquet.Page.Frame) (ordinal : Nat) :
    Except Leaf.Error Encoding :=
  let atPage := Leaf.Error.scalarDispatchPage ordinal frame.header.start
  match pageTag frame with
  | none => .error (atPage .unsupportedPage)
  | some tag =>
    match Encoding.ofTag tag with
    | none => .error (atPage (.unsupportedEncoding tag))
    | some encoding =>
      if declared.contains tag then .ok encoding else .error (atPage (.undeclaredEncoding tag))

/-- PLAIN uses the same exact preparation for V1 and V2 as the standalone readers. -/
def decodePlain (limits : ScalarPage.Limits) (bound : Bound) (codec : Int)
    (frame : Parquet.Page.Frame) (ordinal : Nat) : Except Leaf.Error (List (Option Int64)) := do
  let _ ← (Parquet.Page.Checksum.verify limits.compressedBytes bound.snapshot.bytes frame).mapError
    (.pageChecksum ordinal frame.header.start)
  let atPage := Leaf.Error.scalarDispatchPage ordinal frame.header.start
  let params ← (Timestamp.Page.parameters bound.binding.leaf bound.levels codec frame.value).mapError
    (atPage ∘ .plain)
  (ScalarPage.decode .int64 params limits (Internal.body bound frame)).mapError
    (atPage ∘ .plain ∘ .scalar)

def decodePage (scalars : Limits) (limits : ScalarPage.Limits) (bound : Bound) (codec : Int)
    (declared : List Int) (frame : Parquet.Page.Frame) (ordinal : Nat) : Except Leaf.Error (List (Option Int64)) := do
  match ← route declared frame ordinal with
  | .plain => decodePlain limits bound codec frame ordinal
  | .delta => Delta.decodePage scalars.delta limits bound codec frame ordinal
  | .split => ByteStreamSplit.decodePage scalars.split limits bound codec frame ordinal

def PlainWire (limits : ScalarPage.Limits) (bound : Bound) (codec : Int)
    (frame : Parquet.Page.Frame) (slots : List (Option Int64)) : Prop :=
  let stored := Internal.body bound frame
  ∃ status params layout prepared words,
    Parquet.Page.Checksum.verify limits.compressedBytes bound.snapshot.bytes frame = .ok status ∧
    bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.compressedBytes ∧
    (match status with
      | .absent => frame.value.crc = none
      | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
    Timestamp.Page.parameters bound.binding.leaf bound.levels codec frame.value = .ok params ∧
    params.encoding = 0 ∧
    ScalarPage.validate params limits stored = .ok layout ∧
    ScalarPage.PreparedWire params limits layout stored prepared ∧
    Plain.decodeInt64 (prepared.mask.count true) prepared.scalars = .ok words ∧
    slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words

def PageWire (scalars : Limits) (limits : ScalarPage.Limits) (bound : Bound) (codec : Int)
    (declared : List Int) (frame : Parquet.Page.Frame) (slots : List (Option Int64)) : Prop :=
  slots.length = Internal.pageSlots frame ∧
    ∃ encoding : Encoding, pageTag frame = some encoding.tag ∧ encoding.tag ∈ declared ∧
      match encoding with
      | .plain => PlainWire limits bound codec frame slots
      | .delta => Delta.PageWire scalars.delta limits bound codec frame slots
      | .split => ByteStreamSplit.PageWire scalars.split limits bound codec frame slots

def readGroup (scalars : Limits) (limits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error (Slots bound) := do
  let group ← checkGroup limits bound index
  let metadata := group.chunk.column.metadata
  let pages ← group.frames.zipIdx.mapM fun (frame, ordinal) =>
    decodePage scalars limits.page bound metadata.codec metadata.encodings frame ordinal
  return pages.flatten.map (Option.map bound.binding.descriptor.decode)

def readBound (scalars : Limits) (limits : Leaf.Limits) (bound : Bound) : Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup scalars limits bound)

def convert (scalars : Limits) (inputLimits : Events.ToIpc.Limits)
    (outputLimits : Arrow.ObservationLimits) (input : Bytes) (ordinal : Nat) :
    Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal (readGroup scalars inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch
