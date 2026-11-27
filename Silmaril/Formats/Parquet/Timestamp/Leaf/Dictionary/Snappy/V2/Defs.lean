module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec

/-! Strict modern Snappy dictionary-only TIMESTAMP with Data Page V2. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.V2

/-- Require the original V2 page kind before applying the shared encoding and
schema checks. The original header and body remain the inputs to decoding. -/
def planDataWith (admits : Int → Bool) (bound : Bound)
    (frame : Parquet.Page.Frame) : Except DictionaryPageError DataPage := do
  if let .dictionary _ := frame.value.kind then throw .misplacedDictionary
  let .dataV2 _ := frame.value.kind | throw (.parameters .unsupportedPage)
  Snappy.planDataWith admits bound frame

/-- Only RLE_DICTIONARY is admitted after the leading PLAIN dictionary. -/
def planData := planDataWith (· == 8)

def checkGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error CheckedChunk :=
  Dictionary.checkGroupUsing .snappyDictionary limits leafLimits bound index
    (planData bound) (fun _ => .ok ()) (Snappy.readEntries limits leafLimits bound)

def readGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error (Slots bound) :=
  Snappy.readGroupUsing limits leafLimits bound (checkGroup limits leafLimits bound index)

def readBound (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) : Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Emit one native Arrow batch per footer group for a selected modern leaf. -/
def convert (limits : Dictionary.Limits) (inputLimits : Events.ToIpc.Limits)
    (outputLimits : Arrow.ObservationLimits) (input : Bytes) (ordinal : Nat) :
    Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal
    (readGroup limits inputLimits.leaf)

/-- Exact original stored bytes, raw levels and flag-selected reference suffix. -/
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
    Payload.Decodes (frame.value.uncompressedSize - header.definitionBytes) .snappy storedValues expandedValues
    else storedValues = expandedValues

end Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.V2
