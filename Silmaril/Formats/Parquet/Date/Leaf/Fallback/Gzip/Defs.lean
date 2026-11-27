module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Defs
public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec

/-! Opt-in GZIP DATE with a PLAIN dictionary, a nonempty RLE_DICTIONARY
prefix and a nonempty PLAIN suffix of Data Page V1 frames. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip

open DictionaryChunk (DataPage)

structure Limits extends toDictionaryLimits : Dictionary.Snappy.Limits where
  scalar := ⟨16 * 1024 * 1024, 16 * 1024 * 1024, ⟨1024 * 1024, 16 * 1024 * 1024⟩, 1024 * 1024⟩

abbrev CheckedGroup := Dictionary.Snappy.CheckedGroup

inductive HeaderError where
  | expectedV1
  | encoding (actual : Int)
  deriving DecidableEq, Repr

inductive GroupError where
  | chunk (cause : Dictionary.Snappy.GroupError)
  | header (page offset : Nat) (cause : HeaderError)
  | sequence (cause : Fallback.GroupError)
  | plain (page offset : Nat) (cause : ScalarPage.Error)
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

def readEntries (limits : Limits) (source : Bytes) (frame : Page.Frame) :
    Except Dictionary.Snappy.PageError (List Int32) := do
  let .dictionary header := frame.value.kind | throw .expectedDictionary
  if header.encoding ≠ 0 then throw (.encoding header.encoding)
  if limits.maxEntries < header.numValues then throw .entryLimit
  let bounds := Dictionary.Snappy.dictionaryBounds limits.toDictionaryLimits frame
  let _ ← (Page.Checksum.verify bounds.compressedLimit source frame).mapError .checksum
  let words ← (Payload.decode bounds Payload.Codec.gzip.id
    (Page.Checksum.payloadBytes source frame).toList).mapError .payload
  (Plain.decodeInt32 header.numValues (Bytes.ofList words)).mapError .entries

def planData (bound : Bound) (frame : Page.Frame) : Except HeaderError DataPage := do
  let .dataV1 header := frame.value.kind | throw .expectedV1
  if header.encoding ≠ 8 ∧ header.encoding ≠ 0 then throw (.encoding header.encoding)
  let some params := FlatScan.int32PageParameters bound.field frame.value | throw .expectedV1
  return ⟨frame, { params with codec := Payload.Codec.gzip.id }⟩

def planPages (bound : Bound) (frames : List Page.Frame) : Except GroupError (List DataPage) :=
  Fallback.planPagesWith (planData bound) (fun ordinal frame => GroupError.header ordinal frame.header.start)
    id .sequence frames

def checkGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError CheckedGroup :=
  Dictionary.Snappy.checkGroupWithCodec .gzip .chunk (readEntries limits) (planPages bound) limits.toDictionaryLimits bound index

/-- Verify the original stored body before dispatching to either scalar
decoder. The admitted parameters determine the page version and codec. -/
def decodePageWith {ε : Type} (chunkError : Dictionary.Snappy.GroupError → ε)
    (plainError : Nat → Nat → ScalarPage.Error → ε)
    (limits : Limits) (source : Bytes) (entries : Array Int32)
    (page : DataPage) (ordinal : Nat) : Except ε Slots := do
  let _ ← (Dictionary.Snappy.verifyData limits.toDictionaryLimits source page ordinal).mapError chunkError
  let stored := Page.Checksum.payloadBytes source page.frame
  if page.params.encoding = 0 then
    (ScalarPage.decode .int32 page.params limits.scalar stored).mapError
      (plainError ordinal page.frame.header.start)
  else
    (DictionaryIndex.decode entries page.params limits.scalar limits.indices stored).mapError
      (chunkError ∘ Dictionary.Snappy.atFrame ordinal page.frame ∘ .references)

def decodePage (limits : Limits) (source : Bytes) (entries : Array Int32)
    (page : DataPage) (ordinal : Nat) : Except GroupError Slots :=
  decodePageWith .chunk .plain limits source entries page ordinal

def readGroupWith {ε : Type} (check : Nat → Except ε CheckedGroup)
    (decode : Bytes → Array Int32 → DataPage → Nat → Except ε Slots)
    (bound : Bound) (index : Nat) : Except ε Slots := do
  let checked ← check index
  let entries := checked.entries.toArray
  let pages ← (checked.data.zipIdx 1).mapM fun (page, ordinal) =>
    decode bound.snapshot.bytes entries page ordinal
  return pages.flatten

def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots :=
  readGroupWith (checkGroup limits bound) (decodePage limits) bound index

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Emit complete Date32 IPC only after the original selected source reaches EOF. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

/-- The original frame supplies the exact stored slice and integrity status.
Its entire payload is one bounded GZIP member. -/
structure StoredMember (source : Bytes) (frame : Page.Frame) (storedCap expandedCap : Nat)
    (expanded : List UInt8) : Prop where
  checksum : frame.value.crc = none ∨ ∃ crc, frame.value.crc = some crc ∧
    Compression.crc32Spec (Page.Checksum.payloadBytes source frame).toList = crc
  slice : source.slice? frame.payload.start (some frame.payload.stop) =
    some (Page.Checksum.payloadBytes source frame)
  storedSize : (Page.Checksum.payloadBytes source frame).length = frame.value.compressedSize
  storedBound : frame.value.compressedSize ≤ storedCap
  gzip : Compression.Gzip.decoder (Page.Checksum.payloadBytes source frame).toList = some (expanded, [])
  expandedSize : expanded.length = frame.value.uncompressedSize
  expandedBound : expanded.length ≤ expandedCap

/-- The original V1 frame yields its nullable mask and either ordered
dictionary indices or ordered signed PLAIN words. -/
structure PageWire (limits : Limits) (source : Bytes) (entries : Array Int32) (page : DataPage)
    (slots : Slots) : Prop where
  count : slots.length = page.params.numValues
  wire : ∃ expanded layout sections, ∃ prepared : ScalarPage.Prepared,
    StoredMember source page.frame limits.scalar.compressedBytes limits.scalar.uncompressedBytes expanded ∧
    FlatPage.split layout limits.scalar.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
    FlatPage.readMask layout page.params.numValues limits.scalar.levels sections.definitions =
      .ok prepared.mask ∧
    prepared.scalars = sections.scalars ∧
    slots.map Option.isSome = prepared.mask ∧
    ((page.params.encoding = 8 ∧ ∃ width runs indices,
      prepared.scalars.toList = width :: runs ∧ width.toNat ≤ 32 ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      indices.map (fun index => entries[index]?) = (slots.filterMap id).map some) ∨
      (page.params.encoding = 0 ∧ ScalarPage.Kind.int32.readPlain (prepared.mask.count true)
        prepared.scalars = .ok (slots.filterMap id)))

end Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip
