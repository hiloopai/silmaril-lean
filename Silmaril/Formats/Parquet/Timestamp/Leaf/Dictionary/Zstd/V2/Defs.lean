module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Defs

/-! Strict Zstandard TIMESTAMP chunks with one PLAIN dictionary and only V2 references. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2

structure Limits where
  dictionary : Dictionary.Limits := {}
  maxExpandedChunkBytes : Nat := 64 * 1024 * 1024
  compression : FlatColumn.Zstd.CompressionLimits := ⟨8 * 1024 * 1024, 43690⟩

abbrev GroupError := Leaf.Zstd.V2.GroupError
abbrev Error := Leaf.Zstd.V2.Error

def scalarLimits (limits : Limits) : Leaf.Zstd.V2.Limits :=
  ⟨limits.dictionary.maxChunkBytes, limits.maxExpandedChunkBytes, limits.compression⟩

/-- The leading PLAIN dictionary consumes one bounded Zstandard frame in full. -/
def readEntries (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (frame : Parquet.Page.Frame) :
    Except GroupError (List Int64) := do
  let atDictionary := Leaf.Zstd.V2.GroupError.selection ∘ atFrame 0 frame
  let .dictionary header := frame.value.kind | throw (atDictionary .expectedDictionary)
  if header.encoding ≠ 0 then throw (atDictionary (.encoding header.encoding))
  if limits.dictionary.maxEntries < header.numValues then throw (atDictionary .entryLimit)
  let bounds := Snappy.dictionaryBounds limits.dictionary leafLimits frame
  let _ ← (Parquet.Page.Checksum.verify bounds.compressedLimit bound.snapshot.bytes frame).mapError
    (.checksum 0 frame.header.start)
  let words ← (FlatColumn.Zstd.decodePayload limits.compression bounds Payload.Codec.zstd.id
    (Leaf.Internal.body bound frame).toList).mapError (.decode 0 frame.header.start)
  (Plain.decodeInt64 header.numValues (Bytes.ofList words)).mapError (atDictionary ∘ .entries)

/-- Retain the original V2 reference or value parameters under the chosen data tag policy. -/
def planDataWith (admits : Int → Bool) (bound : Bound) (frame : Parquet.Page.Frame) : Except DictionaryPageError DataPage := do
  if let .dictionary _ := frame.value.kind then throw .misplacedDictionary
  let .dataV2 header := frame.value.kind | throw (.parameters .unsupportedPage)
  if !admits header.encoding then throw (.encoding header.encoding)
  let params ← (Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.zstd.id
    frame.value).mapError .parameters
  return ⟨frame, params⟩

def planData := planDataWith (· == 8)

def planPagesWith (admits : Int → Bool) (bound : Bound) (frames : List Parquet.Page.Frame) :
    Except GroupError (List DataPage) :=
  (frames.zipIdx 1).mapM fun (frame, ordinal) =>
    (planDataWith admits bound frame).mapError (.selection ∘ atFrame ordinal frame)

def planPages := planPagesWith (· == 8)

/-- Check the whole original frame chain and declared expansion before the data
phase and slot checks. Only then expand the leading dictionary. -/
def checkFramedWith (admits : Int → Bool) (validate : List DataPage → Except Leaf.Error Unit)
    (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (framed : FramedChunk) :
    Except GroupError CheckedChunk := do
  if limits.maxExpandedChunkBytes < (framed.frames.map (·.value.uncompressedSize)).sum then
    throw .expandedChunkLimit
  let data ← planPagesWith admits bound framed.data
  (validate data).mapError .selection
  let actual := (data.map (·.params.numValues)).sum
  let expected := framed.chunk.group.numRows.toNat
  if actual ≠ expected then throw (.selection (.rowCount expected actual))
  let entries ← readEntries limits leafLimits bound framed.dictionary
  return ⟨framed.chunk, framed.dictionary, entries, data⟩

def checkGroupWith (admits : Int → Bool) (validate : List DataPage → Except Leaf.Error Unit)
    (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError CheckedChunk := do
  let framed ← (frameGroupUsing .zstdDictionaryV2 limits.dictionary leafLimits bound index).mapError .selection
  checkFramedWith admits validate limits leafLimits bound framed

/-- The strict dictionary-only profile requires tag 8 on every data frame. -/
def checkGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError CheckedChunk :=
  checkGroupWith (· == 8) (fun _ => .ok ()) limits leafLimits bound index

def decodeReferences (limits : Hybrid.Limits) (entries : Array Int64) (prepared : ScalarPage.Prepared) :
    Except DictionaryIndex.Error (List (Option Int64)) := do
  let indices ← DictionaryIndex.readIndices limits (prepared.mask.count true) prepared.scalars
  let values ← DictionaryIndex.select entries indices
  (FlatPage.reconstruct prepared.mask values).mapError .slots

/-- Verify the original CRC before preparing its raw levels and flag-selected references. -/
def decodePage (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (entries : Array Int64)
    (page : DataPage) (ordinal : Nat) : Except GroupError (List (Option Int64)) := do
  let frame := page.frame
  let _ ← (Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes frame).mapError
    (.checksum ordinal frame.header.start)
  let prepared ← (FlatColumn.Zstd.prepareFor 8 (Leaf.Zstd.V2.columnLimits (scalarLimits limits) leafLimits)
    page.params (Leaf.Internal.body bound frame)).mapError (.decode ordinal frame.header.start)
  (decodeReferences limits.dictionary.indices entries prepared).mapError (.references ordinal frame.header.start)

def DictionaryWire (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (frame : Parquet.Page.Frame) (entries : List Int64) : Prop :=
  let stored := Leaf.Internal.body bound frame
  let bounds := Snappy.dictionaryBounds limits.dictionary leafLimits frame
  ∃ (status : Parquet.Page.Checksum.Status), ∃ header expanded parsed,
    frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
    header.numValues ≤ limits.dictionary.maxEntries ∧
    bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ bounds.compressedLimit ∧
    (match status with
     | .absent => frame.value.crc = none
     | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
    Compression.Zstd.CheckedFrame.Huffman.FrameWire (FlatColumn.Zstd.frameLimits limits.compression bounds)
      stored.toList expanded parsed ∧ parsed.windowSize ≤ limits.compression.window ∧
    expanded.length = frame.value.uncompressedSize ∧ expanded.length ≤ bounds.outputLimit ∧
    Plain.decodeInt64 header.numValues (Bytes.ofList expanded) = .ok entries ∧ entries.length = header.numValues

/-- The original stored page binds the exact definition mask and ordered lookup
stream into the dictionary belonging to this chunk. -/
structure PageWire (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (entries : Array Int64) (page : DataPage) (slots : List (Option Int64)) : Prop where
  count : slots.length = page.params.numValues
  original : let frame := page.frame
    let body := Leaf.Internal.body bound frame
    ∃ (status : Parquet.Page.Checksum.Status), ∃ header layout definitions encoded,
      ∃ prepared : ScalarPage.Prepared, ∃ width runs indices,
      frame.value.kind = .dataV2 header ∧ header.encoding = 8 ∧
      bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some body ∧
      body.length = frame.value.compressedSize ∧ frame.value.compressedSize ≤ leafLimits.page.compressedBytes ∧
      frame.value.uncompressedSize ≤ leafLimits.page.uncompressedBytes ∧
      (match status with
       | .absent => frame.value.crc = none
       | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec body.toList = crc) ∧
      header.numRows = header.numValues ∧ header.numNulls ≤ header.numValues ∧
      header.repetitionBytes = 0 ∧ header.definitionBytes ≤ frame.value.compressedSize ∧
      header.definitionBytes ≤ frame.value.uncompressedSize ∧ header.definitionBytes ≤ leafLimits.page.levels.bytes ∧
      definitions.length = header.definitionBytes ∧ body.toList = definitions.toList ++ encoded ∧
      Leaf.Zstd.V2.SuffixWire (scalarLimits limits) leafLimits frame header encoded prepared.scalars.toList ∧
      FlatPage.readMask layout header.numValues leafLimits.page.levels definitions = .ok prepared.mask ∧
      prepared.scalars.length ≤ limits.dictionary.indices.bytes ∧
      prepared.scalars.toList = width :: runs ∧ width.toNat ≤ 32 ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      indices.map (fun index => entries[index]?) = (slots.filterMap id).map some ∧
      slots.map Option.isSome = prepared.mask ∧
      (slots.filterMap id).length + header.numNulls = header.numValues

def readGroupUsing (bound : Bound)
    (decode : Array Int64 → DataPage → Nat → Except GroupError (List (Option Int64)))
    (admitted : Except GroupError CheckedChunk) : Except GroupError (Slots bound) := do
  let checked ← admitted
  let entries := checked.entries.toArray
  let pages ← (checked.data.zipIdx 1).mapM fun (page, ordinal) =>
    decode entries page ordinal
  return pages.flatten.map (Option.map bound.binding.descriptor.decode)

def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError (Slots bound) :=
  readGroupUsing bound (decodePage limits leafLimits bound) (checkGroup limits leafLimits bound index)

def readBound (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) : Leaf.Zstd.V2.Source :=
  Leaf.Zstd.V2.readBoundWith bound (readGroup limits leafLimits bound)

/-- Select the modern dictionary-only Zstandard V2 profile at the original leaf ordinal. -/
def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (output : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Error KBytes :=
  Leaf.Zstd.V2.convertWith inputLimits output input ordinal (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2
