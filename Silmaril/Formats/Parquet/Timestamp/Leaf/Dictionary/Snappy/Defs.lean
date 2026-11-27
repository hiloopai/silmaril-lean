module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Defs

/-! Snappy PLAIN dictionaries and RLE_DICTIONARY TIMESTAMP data pages. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy

def dictionaryBounds (limits : Dictionary.Limits) (leafLimits : Leaf.Limits)
    (frame : Parquet.Page.Frame) : Payload.Bounds :=
  ⟨frame.value.compressedSize, min limits.maxDictionaryBytes leafLimits.page.compressedBytes,
    frame.value.uncompressedSize, min limits.maxDictionaryBytes leafLimits.page.uncompressedBytes,
    leafLimits.page.gzipCalls⟩

/-- Verify the dictionary CRC, when present, over the original stored payload.
The span and caps are checked before Snappy expansion. -/
def readEntries (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (frame : Parquet.Page.Frame) : Except DictionaryPageError (List Int64) := do
  let .dictionary header := frame.value.kind | throw .expectedDictionary
  if header.encoding ≠ 0 then throw (.encoding header.encoding)
  if limits.maxEntries < header.numValues then throw .entryLimit
  let bounds := dictionaryBounds limits leafLimits frame
  if bounds.outputLimit < bounds.expectedSize then throw (.payload .outputLimit)
  let _ ← (Parquet.Page.Checksum.verify bounds.compressedLimit bound.snapshot.bytes frame).mapError
    .checksumFailure
  let body ← (Payload.decode bounds Payload.Codec.snappy.id
    (Leaf.Internal.body bound frame).toList).mapError .payload
  (Plain.decodeInt64 header.numValues (Bytes.ofList body)).mapError .entries

def planDataWith (admits : Int → Bool) (bound : Bound) (frame : Parquet.Page.Frame) :
    Except DictionaryPageError DataPage := do
  if let .dictionary _ := frame.value.kind then throw .misplacedDictionary
  let params ← (Timestamp.Page.parameters bound.binding.leaf bound.levels
    Payload.Codec.snappy.id frame.value).mapError .parameters
  if !admits params.encoding then throw (.encoding params.encoding)
  return ⟨frame, params⟩

def planData (bound : Bound) (frame : Parquet.Page.Frame) :
    Except DictionaryPageError DataPage :=
  planDataWith (· == 8) bound frame

/-- Reuse the checked chunk and require one bounded dictionary and only
RLE_DICTIONARY data pages under the Snappy codec. -/
def checkGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error CheckedChunk :=
  Dictionary.checkGroupUsing .snappyDictionary limits leafLimits bound index
    (planData bound) (fun _ => .ok ()) (readEntries limits leafLimits bound)

/-- Verify the stored extent and any CRC with the original indexed context. -/
def verifyData (leafLimits : Leaf.Limits) (bound : Bound) (page : DataPage) (ordinal : Nat) :
    Except Leaf.Error Parquet.Page.Checksum.Status :=
  (Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame).mapError
    (atFrame ordinal page.frame ∘ .checksumFailure)

/-- Verify the original stored data payload before the shared decoder splits
V2 levels from the value suffix or decompresses the whole V1 body. -/
def decodePage (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (entries : Array Int64) (page : DataPage) (ordinal : Nat) : Except Leaf.Error (List (Option Int64)) := do
  let _ ← verifyData leafLimits bound page ordinal
  Dictionary.decodePage limits leafLimits bound entries page ordinal

/-- The same original frame supplies the checked stored body and index decoder. -/
def DataWire (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (entries : Array Int64) (page : DataPage) (slots : List (Option Int64)) : Prop :=
  ∃ status,
    Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame = .ok status ∧
    DictionaryIndex.decode entries page.params leafLimits.page limits.indices
      (Leaf.Internal.body bound page.frame) = .ok slots

def readGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error (Slots bound) := do
  let checked ← checkGroup limits leafLimits bound index
  let entries := checked.entries.toArray
  let pages ← (checked.data.zipIdx 1).mapM fun (page, ordinal) =>
    decodePage limits leafLimits bound entries page ordinal
  return pages.flatten.map (Option.map bound.binding.descriptor.decode)

def readBound (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Opt in to Snappy dictionary-only reads at the selected TIMESTAMP leaf. -/
def convert (profile : AnnotationProfile) (limits : Dictionary.Limits) (inputLimits : Events.ToIpc.Limits)
    (outputLimits : Arrow.ObservationLimits) (input : Bytes) (ordinal : Nat) :
    Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups profile inputLimits outputLimits input ordinal (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy
