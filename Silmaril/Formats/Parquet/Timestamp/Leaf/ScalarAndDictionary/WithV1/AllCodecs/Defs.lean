module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.Defs

/-! Opt-in modern dictionary TIMESTAMP V1/V2 across all four existing codecs. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs

open Silmaril.Numeric.Timestamp (Ticks)

inductive Codec where
  | uncompressed | zstd
  deriving DecidableEq, Repr

def Codec.branch : Codec → ScalarAndDictionary.Branch
  | .uncompressed => .dictionary .uncompressed
  | .zstd => .dictionary .zstd

def Codec.encoding : Codec → Leaf.ChunkEncoding
  | .uncompressed => .dictionary
  | .zstd => .zstdDictionaryV2

def Codec.payload : Codec → Payload.Codec
  | .uncompressed => .uncompressed
  | .zstd => .zstd

abbrev zstdLimits (limits : Limits) : Dictionary.Zstd.V2.Limits :=
  limits.dictionary.threeCodec.twoCodec.zstd

def Codec.dictionaryLimits (codec : Codec) (limits : Limits) : Dictionary.Limits :=
  match codec with
  | .uncompressed => limits.dictionary.uncompressed
  | .zstd => (zstdLimits limits).dictionary

def Codec.expansionLimit (codec : Codec) (limits : Limits) (framed : Dictionary.FramedChunk) : Prop :=
  match codec with
  | .uncompressed => True
  | .zstd => (framed.frames.map (·.value.uncompressedSize)).sum ≤ (zstdLimits limits).maxExpandedChunkBytes

/-- Reuse the indexed checksum, preparation and reference errors for the two new V1 routes. -/
abbrev V1Error := Leaf.Zstd.V2.GroupError

inductive GroupError where
  | existing (cause : WithV1.GroupError)
  | v1 (codec : Codec) (cause : V1Error)
  deriving DecidableEq, Repr

inductive SourceError where
  | groupFailure (index : Nat) (cause : GroupError)
  deriving DecidableEq, Repr

inductive Error where
  | openFailure (cause : Events.ToIpc.Error)
  | source (cause : SourceError)
  | closed
  | writer (cause : Arrow.TimestampStream.Writer.Error)
  deriving DecidableEq, Repr

def Codec.readEntries (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (frame : Parquet.Page.Frame) : Except V1Error (List Int64) :=
  match codec with
  | .uncompressed =>
    (Dictionary.Uncompressed.V2.readEntries limits.dictionary.uncompressed leafLimits bound frame).mapError
      (.selection ∘ Dictionary.atFrame 0 frame)
  | .zstd => Dictionary.Zstd.V2.readEntries (zstdLimits limits) leafLimits bound frame

def admits (fallback : Bool) (tag : Int) : Bool :=
  tag == 8 || fallback && tag == 0

/-- Pin V1 and the selected modern tag policy before interpreting the original header. -/
def planData (codec : Codec) (fallback : Bool) (bound : Bound) (frame : Parquet.Page.Frame) :
    Except DictionaryPageError Dictionary.DataPage := do
  if let .dictionary _ := frame.value.kind then throw .misplacedDictionary
  let .dataV1 header := frame.value.kind | throw (.parameters .unsupportedPage)
  if !admits fallback header.encoding then throw (.encoding header.encoding)
  let params ← (Timestamp.Page.parameters bound.binding.leaf bound.levels codec.payload.id frame.value).mapError
    .parameters
  return ⟨frame, params⟩

def frameGroup (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error Dictionary.FramedChunk :=
  Dictionary.frameGroupUsing codec.encoding (codec.dictionaryLimits limits) leafLimits bound index

def checkExpansion (codec : Codec) (limits : Limits) (framed : Dictionary.FramedChunk) :
    Except V1Error Unit :=
  match codec with
  | .uncompressed => .ok ()
  | .zstd =>
    if (zstdLimits limits).maxExpandedChunkBytes < (framed.frames.map (·.value.uncompressedSize)).sum then
      .error .expandedChunkLimit
    else .ok ()

def checkFramed (codec : Codec) (fallback : Bool) (limits : Limits) (leafLimits : Leaf.Limits)
    (bound : Bound) (framed : Dictionary.FramedChunk) : Except V1Error Dictionary.CheckedChunk := do
  checkExpansion codec limits framed
  let data ← (framed.data.zipIdx 1).mapM fun (frame, ordinal) =>
    (planData codec fallback bound frame).mapError (.selection ∘ Dictionary.atFrame ordinal frame)
  (WithV1.validate fallback data).mapError .selection
  let actual := (data.map (·.params.numValues)).sum
  let expected := framed.chunk.group.numRows.toNat
  if actual ≠ expected then throw (.selection (.rowCount expected actual))
  else
    let entries ← codec.readEntries limits leafLimits bound framed.dictionary
    return ⟨framed.chunk, framed.dictionary, entries, data⟩

def zstdColumnLimits (limits : Limits) (leafLimits : Leaf.Limits) : FlatColumn.Zstd.Limits :=
  Leaf.Zstd.V2.columnLimits (Dictionary.Zstd.V2.scalarLimits (zstdLimits limits)) leafLimits

def Codec.prepare (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (params : ScalarPage.Parameters)
    (body : Bytes) : Except FlatColumn.Zstd.Error ScalarPage.Prepared :=
  match codec with
  | .uncompressed => (ScalarPage.prepareFor params.encoding params leafLimits.page body).mapError .scalar
  | .zstd => FlatColumn.Zstd.prepareFor params.encoding (zstdColumnLimits limits leafLimits) params body

/-- Verify the original stored body before whole-body preparation and scalar decoding. -/
def decodePage (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (entries : Array Int64) (page : Dictionary.DataPage) (ordinal : Nat) :
    Except V1Error (List (Option Int64)) := do
  let frame := page.frame
  let decodeError := Leaf.Zstd.V2.GroupError.decode ordinal frame.header.start
  let _ ← (Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes frame).mapError
    (.checksum ordinal frame.header.start)
  let prepared ← (codec.prepare limits leafLimits page.params (Leaf.Internal.body bound frame)).mapError decodeError
  if page.params.encoding = 0 then
    let values ← (Plain.decodeInt64 (prepared.mask.count true) prepared.scalars).mapError
      (decodeError ∘ .scalar ∘ .plain)
    (FlatPage.reconstruct prepared.mask values).mapError (decodeError ∘ .scalar ∘ .levels)
  else
    (Dictionary.Zstd.V2.decodeReferences (codec.dictionaryLimits limits).indices entries prepared).mapError
      (.references ordinal frame.header.start)

def readV1 (codec : Codec) (fallback : Bool) (limits : Limits) (leafLimits : Leaf.Limits)
    (bound : Bound) (framed : Dictionary.FramedChunk) : Except V1Error (Slots bound) :=
  Dictionary.Zstd.V2.readGroupUsing bound (decodePage codec limits leafLimits bound)
    (checkFramed codec fallback limits leafLimits bound framed)

def Codec.framingError (codec : Codec) : Leaf.Error → GroupError :=
  match codec with
  | .uncompressed => .existing ∘ .existing ∘ .uncompressedDictionary
  | .zstd => .existing ∘ .existing ∘ .zstdDictionary ∘ .selection

/-- Use the existing strict V2 branches on the retained original frames. -/
def readV2 (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (framed : Dictionary.FramedChunk) : Except GroupError (Slots bound) :=
  match codec with
  | .uncompressed =>
    (Uncompressed.Dispatch.V2.readFramedDictionary limits.dictionary.uncompressed leafLimits bound
      ⟨framed, Uncompressed.Dispatch.V2.scanHeaders bound framed.data 1 false (.ok [])⟩).mapError
      (.existing ∘ .existing ∘ .uncompressedDictionary)
  | .zstd =>
    (Zstd.Dispatch.V2.readFramedDictionary (zstdLimits limits) leafLimits bound framed
      (Zstd.Dispatch.V2.dictionaryProfile framed.data)).mapError (.existing ∘ .existing ∘ .zstdDictionary)

def readDictionary (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except GroupError (Slots bound) := do
  let framed ← (frameGroup codec limits leafLimits bound index).mapError codec.framingError
  let profile ← (WithV1.classifyFrames framed).mapError .existing
  match profile.version with
  | .v1 => (readV1 codec profile.fallback limits leafLimits bound framed).mapError (.v1 codec)
  | .v2 => readV2 codec limits leafLimits bound framed

def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError (Slots bound) := do
  let branch ← (ScalarAndDictionary.route bound index).mapError (.existing ∘ .existing)
  match branch with
  | .dictionary .uncompressed => readDictionary .uncompressed limits leafLimits bound index
  | .dictionary .zstd => readDictionary .zstd limits leafLimits bound index
  | .dictionary .snappy => (WithV1.readDictionary .snappy limits leafLimits bound index).mapError .existing
  | .dictionary .gzip => (WithV1.readDictionary .gzip limits leafLimits bound index).mapError .existing
  | .scalar _ => (ScalarAndDictionary.readSelected limits leafLimits bound index branch).mapError (.existing ∘ .existing)

def trace (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Events.Cell SourceError :=
  MixedCodec.V2.traceUsing bound (readGroup limits leafLimits bound) .groupFailure

def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (output : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Error KBytes := do
  let bound ← (Events.ToIpc.openBound inputLimits input ordinal).mapError .openFailure
  MixedCodec.V2.emitUsing output bound (trace limits inputLimits.leaf bound) .source .closed .writer

/-- The checked size and optional CRC cover exactly the original payload slice. -/
def StoredWire (cap : Nat) (bound : Bound) (frame : Parquet.Page.Frame)
    (status : Parquet.Page.Checksum.Status) : Prop :=
  let stored := Leaf.Internal.body bound frame
  bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ cap ∧
    match status with
    | .absent => frame.value.crc = none
    | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc

/-- The checked dictionary comes from the same original frame with its codec-specific exact byte contract. -/
def EntriesWire (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (frame : Parquet.Page.Frame) (entries : List Int64) : Prop :=
  match codec with
  | .zstd => Dictionary.Zstd.V2.DictionaryWire (zstdLimits limits) leafLimits bound frame entries
  | .uncompressed =>
    let bounds := Dictionary.Snappy.dictionaryBounds limits.dictionary.uncompressed leafLimits frame
    let body := Leaf.Internal.body bound frame
    ∃ header status,
      frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      header.numValues ≤ limits.dictionary.uncompressed.maxEntries ∧
      StoredWire bounds.compressedLimit bound frame status ∧
      body.length = frame.value.uncompressedSize ∧ body.length ≤ bounds.outputLimit ∧
      Plain.decodeInt64 header.numValues body = .ok entries ∧ entries.length = header.numValues

/-- V1 preparation covers the full original body and the checked level/value slices. -/
def PreparedWire (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (params : ScalarPage.Parameters)
    (body : Bytes) (prepared : ScalarPage.Prepared) : Prop :=
  ∃ layout, ScalarPage.validateFor params.encoding params leafLimits.page body = .ok layout ∧
    match codec with
    | .uncompressed => ScalarPage.PreparedWire params leafLimits.page layout body prepared
    | .zstd => FlatColumn.Zstd.PreparedWire (zstdColumnLimits limits leafLimits) params layout body prepared

def PageWire (codec : Codec) (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (entries : Array Int64) (page : Dictionary.DataPage) (slots : List (Option Int64)) : Prop :=
  let frame := page.frame
  let body := Leaf.Internal.body bound frame
  ∃ status prepared,
    StoredWire leafLimits.page.compressedBytes bound frame status ∧
    PreparedWire codec limits leafLimits page.params body prepared ∧
    slots.map Option.isSome = prepared.mask ∧ slots.length = page.params.numValues ∧
    (if page.params.encoding = 0 then
      Plain.decodeInt64 (prepared.mask.count true) prepared.scalars = .ok (slots.filterMap id)
     else
      ∃ indices,
        DictionaryIndex.readIndices (codec.dictionaryLimits limits).indices (prepared.mask.count true)
          prepared.scalars = .ok indices ∧
        indices.map (fun index => entries[index]?) = (slots.filterMap id).map some)

def PlanWire (codec : Codec) (fallback : Bool) (bound : Bound)
    (frame : Parquet.Page.Frame) (page : Dictionary.DataPage) : Prop :=
  page.frame = frame ∧ ∃ header, frame.value.kind = .dataV1 header ∧ admits fallback header.encoding = true ∧
    page.params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
      header.numValues, codec.payload.id, header.encoding,
      .v1 header.definitionLevelEncoding header.repetitionLevelEncoding⟩

def DictionaryWire (codec : Codec) (fallback : Bool) (limits : Limits) (leafLimits : Leaf.Limits)
    (bound : Bound) (index : Nat) (framed : Dictionary.FramedChunk) (slots : Slots bound) : Prop :=
  selectChunkWith codec.encoding leafLimits bound index = .ok framed.chunk ∧
  bound.snapshot.groupAt index = some framed.chunk.group ∧
  framed.chunk.group.columns[bound.ordinal - 1]? = some framed.chunk.column ∧
  framed.chunk.column.metadata.codec = codec.payload.id ∧
  Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes framed.chunk.span = .ok framed.frames ∧
  Parquet.Page.Chain framed.chunk.span framed.chunk.span.start framed.chunk.span.stop framed.frames ∧
  framed.chunk.span.stop - framed.chunk.span.start ≤ (codec.dictionaryLimits limits).maxChunkBytes ∧
  framed.chunk.column.metadata.dictionaryPageOffset = some (framed.dictionary.header.start : Int) ∧
  framed.chunk.column.metadata.dataPageOffset = (framed.firstData.header.start : Int) ∧
  codec.expansionLimit limits framed ∧
  ∃ (checked : Dictionary.CheckedChunk) (pages : List (List (Option Int64))),
    checked.chunk = framed.chunk ∧ checked.dictionary = framed.dictionary ∧
    List.Forall₂ (PlanWire codec fallback bound) framed.data checked.data ∧
    EntriesWire codec limits leafLimits bound framed.dictionary checked.entries ∧
    (fallback = true → Fallback.OrderedWith 8 checked.data) ∧
    List.Forall₂ (PageWire codec limits leafLimits bound checked.entries.toArray) checked.data pages ∧
    slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
    slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
    slots.length = framed.chunk.group.numRows.toNat

def GroupWire (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat)
    (slots : Slots bound) : Prop :=
  WithV1.GroupWire limits leafLimits bound index slots ∨
    ∃ codec framed fallback, ScalarAndDictionary.route bound index = .ok codec.branch ∧
      frameGroup codec limits leafLimits bound index = .ok framed ∧
      WithV1.classifyFrames framed = .ok ⟨.v1, fallback⟩ ∧
      DictionaryWire codec fallback limits leafLimits bound index framed slots

end Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs
