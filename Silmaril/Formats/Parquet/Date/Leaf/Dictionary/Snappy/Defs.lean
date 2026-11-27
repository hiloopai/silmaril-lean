module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Defs

/-! Opt-in Snappy dictionaries for a strictly selected flat DATE leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy

open DictionaryChunk (DataPage)

structure Limits extends DictionaryChunk.Limits where
  maxChunkBytes : Nat := 64 * 1024 * 1024
  maxExpandedChunkBytes : Nat := 64 * 1024 * 1024

inductive PageError where
  | expectedDictionary
  | expectedData
  | encoding (actual : Int)
  | dataOffset
  | entryLimit
  | checksum (cause : Page.Checksum.Error)
  | payload (cause : Payload.Error)
  | entries (cause : Plain.Error)
  | references (cause : DictionaryIndex.Error)
  deriving DecidableEq, Repr

inductive GroupError where
  | selection (cause : Leaf.Error)
  | codec (actual : Int)
  | indexPage
  | rowLimit
  | rowCount (expected : Nat) (declared : Int)
  | chunkLimit
  | expandedChunkLimit
  | framing (cause : Page.Error)
  | missingDictionary
  | missingData
  | dictionaryOffset
  | page (ordinal offset : Nat) (cause : PageError)
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

structure CheckedGroup where
  selection : Leaf.Chunk
  dictionary : Page.Frame
  entries : List Int32
  data : List DataPage

def CheckedGroup.frames (checked : CheckedGroup) : List Page.Frame :=
  checked.dictionary :: checked.data.map (·.frame)

def atFrame (ordinal : Nat) (frame : Page.Frame) : PageError → GroupError :=
  .page ordinal frame.header.start

def dictionaryBounds (limits : Limits) (frame : Page.Frame) : Payload.Bounds :=
  ⟨frame.value.compressedSize, min limits.maxDictionaryBytes limits.scalar.compressedBytes,
    frame.value.uncompressedSize, min limits.maxDictionaryBytes limits.scalar.uncompressedBytes,
    limits.scalar.gzipCalls⟩

/-- Bound and verify the original stored dictionary before decompressing its signed words. -/
def readEntries (limits : Limits) (source : Bytes) (frame : Page.Frame) :
    Except PageError (List Int32) := do
  let .dictionary header := frame.value.kind | throw .expectedDictionary
  if header.encoding ≠ 0 then throw (.encoding header.encoding)
  if limits.maxEntries < header.numValues then throw .entryLimit
  let bounds := dictionaryBounds limits frame
  if bounds.outputLimit < bounds.expectedSize then throw (.payload .outputLimit)
  let _ ← (Page.Checksum.verify bounds.compressedLimit source frame).mapError .checksum
  let expanded ← (Payload.decode bounds Payload.Codec.snappy.id
    (Page.Checksum.payloadBytes source frame).toList).mapError .payload
  (Plain.decodeInt32 header.numValues (Bytes.ofList expanded)).mapError .entries

/-- Preserve the original header parameters and explicitly select the Snappy codec. -/
def planData (bound : Bound) (frame : Page.Frame) : Except PageError DataPage := do
  let some base := FlatScan.int32PageParameters bound.field frame.value | throw .expectedData
  if base.encoding ≠ 8 then throw (.encoding base.encoding)
  return ⟨frame, { base with codec := Payload.Codec.snappy.id }⟩

/-- Use the original selected range and declared offsets. All frame sizes
contribute to the chunk-wide bound on expanded bytes before decoding. -/
def checkGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError CheckedGroup := do
  let selected ← (selectChunk bound index).mapError .selection
  let metadata := selected.column.metadata
  let rows := selected.group.numRows.toNat
  if metadata.codec ≠ Payload.Codec.snappy.id then .error (.codec metadata.codec)
  else if metadata.indexPageOffset.isSome then .error .indexPage
  else if metadata.numValues ≠ (rows : Int) then .error (.rowCount rows metadata.numValues)
  else if limits.maxRows < rows then .error .rowLimit
  else if limits.maxChunkBytes < selected.span.stop - selected.span.start then .error .chunkLimit
  else do
    let frames ← (Page.readChunk limits.page bound.snapshot.bytes selected.span).mapError .framing
    if limits.maxExpandedChunkBytes < (frames.map (·.value.uncompressedSize)).sum then
      .error .expandedChunkLimit
    else do
      let dictionary :: rest := frames | throw .missingDictionary
      if metadata.dictionaryPageOffset ≠ some (dictionary.header.start : Int) then .error .dictionaryOffset
      else do
        let first :: _ := rest | throw .missingData
        if metadata.dataPageOffset ≠ (first.header.start : Int) then .error (atFrame 1 first .dataOffset)
        else do
          let data ← (rest.zipIdx 1).mapM fun (frame, ordinal) =>
            (planData bound frame).mapError (atFrame ordinal frame)
          let declared := (data.map (·.params.numValues)).sum
          if declared ≠ rows then .error (.rowCount rows declared)
          else do
            let entries ← (readEntries limits bound.snapshot.bytes dictionary).mapError (atFrame 0 dictionary)
            return ⟨selected, dictionary, entries, data⟩

/-- The original selected chunk and its typed Snappy framing. -/
structure GroupWire (limits : Limits) (bound : Bound) (index : Nat) (checked : CheckedGroup) : Prop where
  selected : selectChunk bound index = .ok checked.selection
  codec : checked.selection.column.metadata.codec = Payload.Codec.snappy.id
  storedCap : checked.selection.span.stop - checked.selection.span.start ≤ limits.maxChunkBytes
  expandedCap : (checked.frames.map (·.value.uncompressedSize)).sum ≤ limits.maxExpandedChunkBytes
  frames : Page.readChunk limits.page bound.snapshot.bytes checked.selection.span = .ok checked.frames
  chain : Page.Chain checked.selection.span checked.selection.span.start checked.selection.span.stop checked.frames
  dictionaryOffset : checked.selection.column.metadata.dictionaryPageOffset =
    some (checked.dictionary.header.start : Int)
  dataOffset : checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
    some checked.selection.column.metadata.dataPageOffset
  dictionary : readEntries limits bound.snapshot.bytes checked.dictionary = .ok checked.entries
  data : ∀ page ∈ checked.data, planData bound page.frame = .ok page
  rows : (checked.data.map (·.params.numValues)).sum = checked.selection.group.numRows.toNat

/-- The page checksum covers the stored V1 body or the entire stored V2
body, including the raw level prefix. ScalarPage handles V2's compression flag. -/
def decodePage (limits : Limits) (source : Bytes) (entries : Array Int32)
    (page : DataPage) (ordinal : Nat) : Except GroupError Slots := do
  let _ ← (Page.Checksum.verify limits.scalar.compressedBytes source page.frame).mapError
    (atFrame ordinal page.frame ∘ .checksum)
  (DictionaryIndex.decode entries page.params limits.scalar limits.indices
    (Page.Checksum.payloadBytes source page.frame)).mapError (atFrame ordinal page.frame ∘ .references)

def PageWire (limits : Limits) (source : Bytes) (entries : Array Int32) (page : DataPage)
    (slots : Slots) : Prop :=
  ∃ status, Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .ok status ∧
    DictionaryIndex.decode entries page.params limits.scalar limits.indices
      (Page.Checksum.payloadBytes source page.frame) = .ok slots

def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  let checked ← checkGroup limits bound index
  let entries := checked.entries.toArray
  let pages ← (checked.data.zipIdx 1).mapM fun (page, ordinal) =>
    decodePage limits bound.snapshot.bytes entries page ordinal
  return pages.flatten

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Emit native Date32 IPC after the selected source reaches EOF. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

end Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy
