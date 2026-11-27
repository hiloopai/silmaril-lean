module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec

/-! Opt-in GZIP V1 TIMESTAMP with a single PLAIN dictionary per chunk. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip

structure Limits where
  dictionary : Dictionary.Limits := {}
  /-- Maximum controller calls for each original GZIP member. -/
  gzipCalls : Nat := 65536

def Limits.withFuel (limits : Limits) (leafLimits : Leaf.Limits) : Leaf.Limits :=
  {leafLimits with page.gzipCalls := limits.gzipCalls}

def readEntries (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (frame : Parquet.Page.Frame) : Except DictionaryPageError (List Int64) :=
  Snappy.readEntriesWithCodec .gzip .plain limits.dictionary (limits.withFuel leafLimits) bound frame

/-- Admit only modern RLE_DICTIONARY V1 data headers with the original GZIP codec. -/
def planData (bound : Bound) (frame : Parquet.Page.Frame) : Except DictionaryPageError DataPage := do
  if let .dictionary _ := frame.value.kind then throw .misplacedDictionary
  let .dataV1 header := frame.value.kind | throw (.parameters .unsupportedPage)
  if header.encoding ≠ 8 then throw (.encoding header.encoding)
  let params ← (Timestamp.Page.parameters bound.binding.leaf bound.levels
    Payload.Codec.gzip.id frame.value).mapError .parameters
  return ⟨frame, params⟩

def checkGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error CheckedChunk :=
  Dictionary.checkGroupUsing .gzipDictionaryV1 limits.dictionary leafLimits bound index
    (planData bound) (fun _ => .ok ()) (readEntries limits leafLimits bound)

def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error (Slots bound) :=
  Snappy.readGroupUsing limits.dictionary (limits.withFuel leafLimits) bound (checkGroup limits leafLimits bound index)

def readBound (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Convert a checked modern flat TIMESTAMP from codec-2 dictionary-only V1 chunks. -/
def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (outputLimits : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal
    (readGroup limits inputLimits.leaf)

/-- The certified original stored payload is exactly one GZIP member, with
separate Parquet and member checksum evidence. -/
structure StoredMember (bound : Bound) (frame : Parquet.Page.Frame) (storedCap expandedCap : Nat)
    (expanded : List UInt8) : Prop where
  slice : bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) =
    some (Leaf.Internal.body bound frame)
  storedSize : (Leaf.Internal.body bound frame).length = frame.value.compressedSize
  storedBound : frame.value.compressedSize ≤ storedCap
  checksum : frame.value.crc = none ∨ ∃ crc, frame.value.crc = some crc ∧
    Compression.crc32Spec (Leaf.Internal.body bound frame).toList = crc
  member : Compression.Gzip.decoder (Leaf.Internal.body bound frame).toList = some (expanded, [])
  trailer : ∃ prefixBytes, (Leaf.Internal.body bound frame).toList =
    prefixBytes ++ Compression.Gzip.trailer expanded
  expandedSize : expanded.length = frame.value.uncompressedSize
  expandedBound : expanded.length ≤ expandedCap

end Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip
