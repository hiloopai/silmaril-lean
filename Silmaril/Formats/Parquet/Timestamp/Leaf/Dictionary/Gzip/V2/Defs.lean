module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.Defs

/-! Opt-in GZIP dictionary-only TIMESTAMP with raw Data Page V2 levels. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2

abbrev Limits := Gzip.Limits

/-- Admit the original dictionary-encoded V2 header and retain its storage flag. -/
def planData (bound : Bound) (frame : Parquet.Page.Frame) : Except DictionaryPageError DataPage := do
  if let .dictionary _ := frame.value.kind then throw .misplacedDictionary
  let .dataV2 header := frame.value.kind | throw (.parameters .unsupportedPage)
  if header.encoding ≠ 8 then throw (.encoding header.encoding)
  let params ← (Timestamp.Page.parameters bound.binding.leaf bound.levels
    Payload.Codec.gzip.id frame.value).mapError .parameters
  return ⟨frame, params⟩

def checkGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error CheckedChunk :=
  Dictionary.checkGroupUsing .gzipDictionaryV2 limits.dictionary leafLimits bound index
    (planData bound) (fun _ => .ok ()) (Gzip.readEntries limits leafLimits bound)

def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error (Slots bound) :=
  Snappy.readGroupUsing limits.dictionary (limits.withFuel leafLimits) bound
    (checkGroup limits leafLimits bound index)

def readBound (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) : Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Convert a selected modern TIMESTAMP leaf with one PLAIN dictionary and only V2 references. -/
def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (outputLimits : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal
    (readGroup limits inputLimits.leaf)

/-- The original stored CRC covers both the raw levels and the stored value
suffix. Only the suffix can be a GZIP member. -/
structure BodyWire (bound : Bound) (frame : Parquet.Page.Frame) (limits : ScalarPage.Limits)
    (header : Parquet.Page.DataV2) (definitions : Bytes) (storedValues expandedValues : List UInt8) : Prop where
  slice : bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) =
    some (Leaf.Internal.body bound frame)
  storedSize : (Leaf.Internal.body bound frame).length = frame.value.compressedSize
  storedBound : frame.value.compressedSize ≤ limits.compressedBytes
  checksum : frame.value.crc = none ∨ ∃ crc, frame.value.crc = some crc ∧
    Compression.crc32Spec (Leaf.Internal.body bound frame).toList = crc
  expandedBound : frame.value.uncompressedSize ≤ limits.uncompressedBytes
  noRepetition : header.repetitionBytes = 0
  definitionSize : definitions.length = header.definitionBytes
  definitionBound : header.definitionBytes ≤ limits.levels.bytes
  definitionFits : header.definitionBytes ≤ frame.value.compressedSize ∧
    header.definitionBytes ≤ frame.value.uncompressedSize
  split : (Leaf.Internal.body bound frame).toList = definitions.toList ++ storedValues
  storedValuesSize : storedValues.length = frame.value.compressedSize - header.definitionBytes
  expandedValuesSize : expandedValues.length = frame.value.uncompressedSize - header.definitionBytes
  compression : if header.isCompressed then
    Compression.Gzip.decoder storedValues = some (expandedValues, []) ∧
      ∃ prefixBytes, storedValues = prefixBytes ++ Compression.Gzip.trailer expandedValues
    else storedValues = expandedValues

end Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2
