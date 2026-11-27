module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs

/-! Uncompressed PLAIN INT64 dictionaries and RLE_DICTIONARY TIMESTAMP data. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary

structure Limits where
  maxChunkBytes : Nat := 64 * 1024 * 1024
  maxEntries : Nat := 1024 * 1024
  maxDictionaryBytes : Nat := 8 * 1024 * 1024
  indices : Hybrid.Limits := ⟨1024 * 1024, 16 * 1024 * 1024⟩

structure DataPage where
  frame : Parquet.Page.Frame
  params : ScalarPage.Parameters

structure CheckedChunk where
  chunk : Leaf.Chunk
  dictionary : Parquet.Page.Frame
  entries : List Int64
  data : List DataPage

def CheckedChunk.frames (checked : CheckedChunk) : List Parquet.Page.Frame :=
  checked.dictionary :: checked.data.map (·.frame)

def atFrame (index : Nat) (frame : Parquet.Page.Frame) : DictionaryPageError → Leaf.Error :=
  .dictionaryPage index frame.header.start

/-- Read exact signed PLAIN words with the entry and body bounds checked before
taking the source slice. The dictionary belongs only to this chunk. -/
def readEntries (limits : Limits) (bound : Bound) (frame : Parquet.Page.Frame) :
    Except DictionaryPageError (List Int64) := do
  let .dictionary header := frame.value.kind | throw .expectedDictionary
  if frame.value.crc.isSome then throw .checksum
  if header.encoding ≠ 0 then throw (.encoding header.encoding)
  if frame.value.compressedSize ≠ frame.value.uncompressedSize then throw .sizeMismatch
  if limits.maxEntries < header.numValues then throw .entryLimit
  if limits.maxDictionaryBytes < frame.value.compressedSize then throw .byteLimit
  (Plain.decodeInt64 header.numValues (Internal.body bound frame)).mapError .entries

def planDataWith (admits : Int → Bool) (bound : Bound) (frame : Parquet.Page.Frame) :
    Except DictionaryPageError DataPage := do
  if let .dictionary _ := frame.value.kind then throw .misplacedDictionary
  if frame.value.crc.isSome then throw .checksum
  if frame.value.compressedSize ≠ frame.value.uncompressedSize then throw .sizeMismatch
  let params ← (Timestamp.Page.parameters bound.binding.leaf bound.levels 0 frame.value).mapError .parameters
  if !admits params.encoding then throw (.encoding params.encoding)
  return ⟨frame, params⟩

def planData (bound : Bound) (frame : Parquet.Page.Frame) : Except DictionaryPageError DataPage :=
  planDataWith (· == 8) bound frame

/-- The original selected chunk and its dictionary and nonempty data frame list. -/
structure FramedChunk where
  chunk : Leaf.Chunk
  dictionary : Parquet.Page.Frame
  firstData : Parquet.Page.Frame
  remainingData : List Parquet.Page.Frame

def FramedChunk.data (framed : FramedChunk) : List Parquet.Page.Frame :=
  framed.firstData :: framed.remainingData

def FramedChunk.frames (framed : FramedChunk) : List Parquet.Page.Frame :=
  framed.dictionary :: framed.data

/-- Read the selected original chunk once and check the two footer offsets. -/
def frameGroupUsing (encoding : Leaf.ChunkEncoding) (limits : Limits) (leafLimits : Leaf.Limits)
    (bound : Bound) (index : Nat) : Except Leaf.Error FramedChunk := do
  let chunk ← selectChunkWith encoding leafLimits bound index
  if limits.maxChunkBytes < chunk.span.stop - chunk.span.start then throw .dictionaryChunkLimit
  let frames ← (Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes chunk.span).mapError .framing
  let dictionary :: rest := frames | throw .dictionaryMissing
  if chunk.column.metadata.dictionaryPageOffset ≠ some (dictionary.header.start : Int) then
    throw .dictionaryOffset
  let first :: following := rest | throw .dictionaryMissingData
  if chunk.column.metadata.dataPageOffset ≠ (first.header.start : Int) then
    throw (atFrame 1 first .dataOffset)
  return ⟨chunk, dictionary, first, following⟩

/-- Finish a framed dictionary chunk whose data headers have already been planned. -/
def checkPlannedUsing (framed : FramedChunk) (data : List DataPage)
    (validate : List DataPage → Except Leaf.Error Unit)
    (read : Parquet.Page.Frame → Except DictionaryPageError (List Int64)) :
    Except Leaf.Error CheckedChunk := do
  validate data
  let expected := framed.chunk.group.numRows.toNat
  let actual := (data.map (·.params.numValues)).sum
  if actual ≠ expected then throw (.rowCount expected actual)
  let entries ← (read framed.dictionary).mapError (atFrame 0 framed.dictionary)
  return ⟨framed.chunk, framed.dictionary, entries, data⟩

/-- Check the selected profile's headers and row total before decoding the
leading dictionary. -/
def checkFramedUsing (framed : FramedChunk)
    (plan : Parquet.Page.Frame → Except DictionaryPageError DataPage)
    (validate : List DataPage → Except Leaf.Error Unit)
    (read : Parquet.Page.Frame → Except DictionaryPageError (List Int64)) :
    Except Leaf.Error CheckedChunk := do
  let data ← (framed.data.zipIdx 1).mapM fun (frame, ordinal) =>
    (plan frame).mapError (atFrame ordinal frame)
  checkPlannedUsing framed data validate read

/-- Share the original checked dictionary framing between data profiles. -/
def checkGroupUsing (encoding : Leaf.ChunkEncoding) (limits : Limits) (leafLimits : Leaf.Limits)
    (bound : Bound) (index : Nat)
    (plan : Parquet.Page.Frame → Except DictionaryPageError DataPage)
    (validate : List DataPage → Except Leaf.Error Unit)
    (read : Parquet.Page.Frame → Except DictionaryPageError (List Int64)) :
    Except Leaf.Error CheckedChunk := do
  let framed ← frameGroupUsing encoding limits leafLimits bound index
  checkFramedUsing framed plan validate read

/-- Use the original uncompressed dictionary and header policy. -/
def checkGroupWith (admits : Int → Bool) (validate : List DataPage → Except Leaf.Error Unit)
    (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) : Except Leaf.Error CheckedChunk :=
  checkGroupUsing .dictionary limits leafLimits bound index
    (planDataWith admits bound) validate (readEntries limits bound)

/-- Admit only RLE_DICTIONARY data after the leading PLAIN dictionary. -/
def checkGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error CheckedChunk :=
  checkGroupWith (· == 8) (fun _ => .ok ()) limits leafLimits bound index

def decodePage (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (entries : Array Int64) (page : DataPage) (ordinal : Nat) :
    Except Leaf.Error (List (Option Int64)) :=
  (DictionaryIndex.decode entries page.params leafLimits.page limits.indices
    (Internal.body bound page.frame)).mapError (atFrame ordinal page.frame ∘ .references)

/-- Resolve each present value against its chunk-local dictionary and preserve
its signed count and the selected annotation. -/
def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error (Slots bound) := do
  let checked ← checkGroup limits leafLimits bound index
  let entries := checked.entries.toArray
  let pages ← (checked.data.zipIdx 1).mapM fun (page, ordinal) =>
    decodePage limits leafLimits bound entries page ordinal
  return pages.flatten.map (Option.map bound.binding.descriptor.decode)

/-- Emit checked footer-order events using only dictionary data pages. -/
def readBound (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) : Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Explicitly opt in to dictionary-only reading of the selected leaf. -/
def convert (profile : AnnotationProfile) (limits : Limits) (inputLimits : Events.ToIpc.Limits)
    (outputLimits : Arrow.ObservationLimits) (input : Bytes) (ordinal : Nat) :
    Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups profile inputLimits outputLimits input ordinal (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary
