module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Delta.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.ByteStreamSplit.Defs

/-! Dictionary-free mixed scalar data pages on one selected INT64 TIMESTAMP leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch

structure Limits where
  delta : DeltaBinaryPacked.Limits := Delta.defaultLimits
  split : Parquet.ByteStreamSplit.Limits := ByteStreamSplit.defaultLimits
  gzipCalls : Nat := 65536
  zstd : FlatColumn.Zstd.CompressionLimits := ⟨8 * 1024 * 1024, 43690⟩

def Limits.pageFor (scalars : Limits) (limits : ScalarPage.Limits) (codec : Int) : ScalarPage.Limits :=
  if codec = 2 then {limits with gzipCalls := scalars.gzipCalls} else limits

def Limits.zstdPage (scalars : Limits) (limits : ScalarPage.Limits) : FlatColumn.Zstd.Limits :=
  ⟨{}, limits, scalars.zstd⟩

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

def decodeZstdValues (scalars : Limits) (encoding : Encoding) (prepared : ScalarPage.Prepared)
    (frame : Parquet.Page.Frame) (ordinal : Nat) : Except Leaf.Error (List Int64) :=
  let count := prepared.mask.count true
  match encoding with
  | .plain => (Plain.decodeInt64 count prepared.scalars).mapError fun cause =>
      .scalarDispatchPage ordinal frame.header.start (.zstd (.scalar (.plain cause)))
  | .delta => (DeltaBinaryPacked.decode .int64 scalars.delta count prepared.scalars).mapError fun cause =>
      .deltaPage ordinal frame.header.start (.decode (.binaryPacked cause))
  | .split => (Parquet.ByteStreamSplit.decode .int64 scalars.split count prepared.scalars).mapError fun cause =>
      .byteStreamSplitPage ordinal frame.header.start (.decode (.scalar cause))

/-- Codec 6 has a checked preparation path for both page versions and each selected value tag. -/
def decodeZstd (scalars : Limits) (limits : ScalarPage.Limits) (bound : Bound)
    (encoding : Encoding) (frame : Parquet.Page.Frame) (ordinal : Nat) :
    Except Leaf.Error (List (Option Int64)) := do
  let _ ← (Parquet.Page.Checksum.verify limits.compressedBytes bound.snapshot.bytes frame).mapError
    (.pageChecksum ordinal frame.header.start)
  let atPage := Leaf.Error.scalarDispatchPage ordinal frame.header.start
  let params ← (Timestamp.Page.parameters bound.binding.leaf bound.levels 6 frame.value).mapError
    (atPage ∘ .zstdParameters)
  let prepared ← (FlatColumn.Zstd.prepareFor encoding.tag (scalars.zstdPage limits) params
    (Internal.body bound frame)).mapError (atPage ∘ .zstd)
  let values ← decodeZstdValues scalars encoding prepared frame ordinal
  (FlatPage.reconstruct prepared.mask values).mapError (atPage ∘ .zstd ∘ .scalar ∘ .levels)

def decodeSelected (scalars : Limits) (limits : ScalarPage.Limits) (bound : Bound) (codec : Int)
    (encoding : Encoding) (frame : Parquet.Page.Frame) (ordinal : Nat) : Except Leaf.Error (List (Option Int64)) :=
  if codec = 6 then decodeZstd scalars limits bound encoding frame ordinal
  else
    let page := scalars.pageFor limits codec
    match encoding with
    | .plain => decodePlain page bound codec frame ordinal
    | .delta => Delta.decodePage scalars.delta page bound codec frame ordinal
    | .split => ByteStreamSplit.decodePage scalars.split page bound codec frame ordinal

def decodePage (scalars : Limits) (limits : ScalarPage.Limits) (bound : Bound) (codec : Int)
    (declared : List Int) (frame : Parquet.Page.Frame) (ordinal : Nat) : Except Leaf.Error (List (Option Int64)) := do
  let encoding ← route declared frame ordinal
  decodeSelected scalars limits bound codec encoding frame ordinal

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

def ZstdValuesWire (scalars : Limits) (encoding : Encoding) (page : ScalarPage.Prepared)
    (values : List Int64) : Prop :=
  let count := page.mask.count true
  values.length = count ∧
    match encoding with
    | .plain => Plain.decodeInt64 count page.scalars = .ok values
    | .delta => ∃ stream : DeltaBinaryPacked.Stream,
        page.scalars.length ≤ scalars.delta.bytes ∧ page.scalars.toList = stream.wire ∧
        stream.Valid .int64 scalars.delta count ∧ values = stream.reconstruct .int64
    | .split => ∃ words,
        Parquet.ByteStreamSplit.Admission scalars.split 8 count page.scalars ∧
        Parquet.ByteStreamSplit.LaneOrder 8 count page.scalars words ∧
        values = words.map (fun word => (Plain.readUInt64Word word).toInt64)

def ZstdWire (scalars : Limits) (limits : ScalarPage.Limits) (bound : Bound) (encoding : Encoding)
    (frame : Parquet.Page.Frame) (slots : List (Option Int64)) : Prop :=
  let stored := Internal.body bound frame
  ∃ status params layout prepared values,
    Parquet.Page.Checksum.verify limits.compressedBytes bound.snapshot.bytes frame = .ok status ∧
    bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.compressedBytes ∧
    frame.value.uncompressedSize ≤ limits.uncompressedBytes ∧
    (match status with
      | .absent => frame.value.crc = none
      | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
    Timestamp.Page.parameters bound.binding.leaf bound.levels 6 frame.value = .ok params ∧
    params.encoding = encoding.tag ∧
    ScalarPage.validateFor encoding.tag params limits stored = .ok layout ∧
    FlatColumn.Zstd.PreparedWire (scalars.zstdPage limits) params layout stored prepared ∧
    ZstdValuesWire scalars encoding prepared values ∧
    slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = values

def PageWire (scalars : Limits) (limits : ScalarPage.Limits) (bound : Bound) (codec : Int)
    (declared : List Int) (frame : Parquet.Page.Frame) (slots : List (Option Int64)) : Prop :=
  slots.length = Internal.pageSlots frame ∧
    ∃ encoding : Encoding, pageTag frame = some encoding.tag ∧ encoding.tag ∈ declared ∧
      if codec = 6 then ZstdWire scalars limits bound encoding frame slots
      else
        let page := scalars.pageFor limits codec
        match encoding with
        | .plain => PlainWire page bound codec frame slots
        | .delta => Delta.PageWire scalars.delta page bound codec frame slots
        | .split => ByteStreamSplit.PageWire scalars.split page bound codec frame slots

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
