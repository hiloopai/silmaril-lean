module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Defs
public import Silmaril.Formats.Parquet.DictionaryIndex.Defs

/-! One original PLAIN INT32 dictionary followed by Snappy RLE_DICTIONARY V1
data pages in the canonical nullable LIST chunk. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1

open Snappy (Budget)
open ListPage (Event State Row)

structure Limits where
  snappy : Snappy.Limits := {}
  maxEntries : Nat := 1024 * 1024
  maxDictionaryBytes : Nat := 4 * 1024 * 1024
  indices : Hybrid.Limits := ⟨1024 * 1024, 16 * 1024 * 1024⟩

inductive FrameError where
  | expectedDictionary
  | expectedDataV1
  | v2 (cause : Snappy.FrameError)
  | dictionaryEncoding (actual : Int)
  | dataEncoding (actual : Int)
  | levelEncoding
  | entryLimit
  | dictionarySize (expected actual : Nat)
  | slotBudget (remaining actual : Nat)
  | expandedBudget (remaining actual : Nat)
  | checksum (cause : Page.Checksum.Error)
  | payload (cause : Payload.Error)
  | entries (cause : Plain.Error)
  | indices (cause : DictionaryIndex.Error)
  | page (cause : ListPage.Error)
  | indexedContinuation
  | fallbackExpectedDictionary
  | dictionaryReentry
  deriving DecidableEq, Repr

inductive GroupError where
  | framing (cause : ListFile.ReadError)
  | missingDictionary
  | missingData
  | missingPlainSuffix
  | dictionaryOffset (declared : Option Int) (actual : Nat)
  | dataOffset (declared : Int) (actual : Nat)
  | slotLimit
  | rowLimit
  | missingSlots (count : Nat)
  | rowCount (expected actual : Nat)
  | frame (ordinal offset : Nat) (cause : FrameError)
  deriving DecidableEq, Repr

inductive SourceError where
  | openFailure (cause : ListFile.OpenError)
  | groupFailure (ordinal : Nat) (cause : GroupError)
  deriving DecidableEq, Repr

inductive Error where
  | source (cause : SourceError)
  | writer (cause : Arrow.ListInt32.Stream.Writer.Error)
  deriving DecidableEq, Repr

def errors : Snappy.ConversionErrors GroupError SourceError Error :=
  ⟨.openFailure, .groupFailure, .source, .writer⟩

def dictionaryStoredCap (limits : Limits) : Nat :=
  min limits.snappy.maxStoredPageBytes limits.maxDictionaryBytes

def dictionaryExpandedCap (limits : Limits) (checked : ListFile.Checked) : Nat :=
  min limits.maxDictionaryBytes checked.limits.page.maxBodyBytes

/-- Verify the original stored bytes before expanding the exact full V1 body. -/
def expand (storedCap expandedCap : Nat) (source : Bytes) (frame : Page.Frame) : Except FrameError Bytes := do
  let _ ← (Page.Checksum.verify storedCap source frame).mapError .checksum
  let bounds : Payload.Bounds :=
    ⟨frame.value.compressedSize, storedCap, frame.value.uncompressedSize, expandedCap, 0⟩
  let expanded ← (Payload.decode bounds 1 (Page.Checksum.payloadBytes source frame).toList).mapError .payload
  pure (Bytes.ofList expanded)

structure ExpandedWire (storedCap expandedCap : Nat) (source : Bytes) (frame : Page.Frame)
    (expanded : Bytes) : Prop where
  data : ∃ status stored,
    Page.Checksum.verify storedCap source frame = .ok status ∧
    source.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ storedCap ∧
    expanded.length = frame.value.uncompressedSize ∧ expanded.length ≤ expandedCap ∧
    Payload.Decodes frame.value.uncompressedSize .snappy stored.toList expanded.toList

/-- The leading dictionary consists of exactly the advertised signed words. -/
def readEntries (limits : Limits) (checked : ListFile.Checked) (expanded : Nat)
    (frame : Page.Frame) : Except FrameError (List Int32) := do
  let .dictionary info := frame.value.kind | throw .expectedDictionary
  if info.encoding ≠ 0 then return ← throw (.dictionaryEncoding info.encoding)
  if limits.maxEntries < info.numValues then return ← throw .entryLimit
  if frame.value.uncompressedSize ≠ info.numValues * 4 then
    return ← throw (.dictionarySize (info.numValues * 4) frame.value.uncompressedSize)
  if expanded < frame.value.uncompressedSize then
    return ← throw (.expandedBudget expanded frame.value.uncompressedSize)
  let body ← expand (dictionaryStoredCap limits) (dictionaryExpandedCap limits checked) checked.snapshot.bytes frame
  (Plain.decodeInt32 info.numValues body).mapError .entries

structure DictionaryWire (limits : Limits) (checked : ListFile.Checked) (frame : Page.Frame)
    (entries : List Int32) : Prop where
  data : ∃ info body,
    frame.value.kind = .dictionary info ∧ info.encoding = 0 ∧ info.numValues ≤ limits.maxEntries ∧
    frame.value.uncompressedSize = info.numValues * 4 ∧
    ExpandedWire (dictionaryStoredCap limits) (dictionaryExpandedCap limits checked) checked.snapshot.bytes frame body ∧
    Plain.decodeInt32 info.numValues body = .ok entries ∧ entries.length = info.numValues

def readValues (limits : Limits) (entries : Array Int32) (present : Nat) (indices : Bytes) :
    Except FrameError (List Int32) := do
  let ordered ← (DictionaryIndex.readIndices limits.indices present indices).mapError .indices
  (DictionaryIndex.select entries ordered).mapError .indices

structure LookupWire (limits : Limits) (entries : Array Int32) (present : Nat)
    (source : Bytes) (values : List Int32) : Prop where
  data : ∃ (width : UInt8) (runs : List UInt8) (indices : List Nat),
    source.toList = width :: runs ∧ width.toNat ≤ 32 ∧
    source.length ≤ limits.indices.bytes ∧ present ≤ limits.indices.values ∧
    Hybrid.Wire width.toNat present runs indices ∧
    indices.length = present ∧ values.length = present ∧
    indices.map (fun i => entries[i]?) = values.map some ∧
    ∀ i, i ∈ indices → i < entries.size

def readFrame (limits : Limits) (checked : ListFile.Checked) (column : Footer.ColumnChunk)
    (entries : Array Int32) (budget : Budget) (frame : Page.Frame) : Except FrameError (List Event) := do
  let .dataV1 info := frame.value.kind | throw .expectedDataV1
  if info.encoding ≠ 8 then return ← throw (.dataEncoding info.encoding)
  if info.repetitionLevelEncoding ≠ 3 ∨ info.definitionLevelEncoding ≠ 3 then return ← throw .levelEncoding
  if budget.slots < info.numValues then return ← throw (.slotBudget budget.slots info.numValues)
  if budget.expanded < frame.value.uncompressedSize then
    return ← throw (.expandedBudget budget.expanded frame.value.uncompressedSize)
  let body ← expand limits.snappy.maxStoredPageBytes checked.limits.page.maxBodyBytes checked.snapshot.bytes frame
  let events ← ListPage.decodeEventsUsing FrameError.page (readValues limits entries) checked.limits.page info.numValues body
  if column.offsetIndexOffset.isSome && Multi.startsWithinRow events then return ← throw .indexedContinuation
  pure events

structure FrameWire (limits : Limits) (checked : ListFile.Checked) (column : Footer.ColumnChunk)
    (entries : Array Int32) (frame : Page.Frame) (events : List Event) : Prop where
  data : ∃ info body,
    frame.value.kind = .dataV1 info ∧ info.encoding = 8 ∧
    info.repetitionLevelEncoding = 3 ∧ info.definitionLevelEncoding = 3 ∧
    ExpandedWire limits.snappy.maxStoredPageBytes checked.limits.page.maxBodyBytes checked.snapshot.bytes frame body ∧
    ListPage.EventsWireUsing (readValues limits entries) checked.limits.page info.numValues body events
  indexBoundary : column.offsetIndexOffset.isSome = true → Multi.startsWithinRow events = false

abbrev FrameReader := Budget → Page.Frame → Except FrameError (List Event)

abbrev DataReader := ListFile.Checked → Footer.ColumnChunk → Array Int32 → FrameReader

abbrev DataWitness := ListFile.Checked → Footer.ColumnChunk → Array Int32 → Page.Frame → List Event → Prop

/-- The selected data callback is applied in original order with a single
chunk-local dictionary and the remaining slot and expansion budgets. -/
def readFramesUsing (read : FrameReader) (ordinal : Nat) (budget : Budget) (state : State) :
    List Page.Frame → Except GroupError (Budget × State)
  | [] => .ok (budget, state)
  | frame :: rest => do
    let events ← (read budget frame).mapError (.frame ordinal frame.header.start)
    let next ← (state.feed events).mapError (.frame ordinal frame.header.start ∘ .page)
    readFramesUsing read (ordinal + 1) (budget.use frame events) next rest

def readFrames (limits : Limits) (checked : ListFile.Checked) (column : Footer.ColumnChunk)
    (entries : Array Int32) (ordinal : Nat) (budget : Budget) (state : State) (frames : List Page.Frame) :
    Except GroupError (Budget × State) :=
  readFramesUsing (readFrame limits checked column entries) ordinal budget state frames

structure Chunk where
  framed : ListFile.FramedGroup
  dictionary : Page.Frame
  firstData : Page.Frame
  rest : List Page.Frame

/-- Select the exact original local chunk and require both advertised frame offsets. -/
def selectChunk (checked : ListFile.Checked) (ordinal : Nat) : Except GroupError Chunk := do
  let framed ← (checked.frameGroupWith 1 true ordinal).mapError .framing
  let dictionary :: data := framed.frames | throw .missingDictionary
  let first :: rest := data | throw .missingData
  let metadata := framed.chunk.metadata
  if metadata.dictionaryPageOffset ≠ some (dictionary.header.start : Int) then
    return ← throw (.dictionaryOffset metadata.dictionaryPageOffset dictionary.header.start)
  if metadata.dataPageOffset ≠ (first.header.start : Int) then
    return ← throw (.dataOffset metadata.dataPageOffset first.header.start)
  pure ⟨framed, dictionary, first, rest⟩

structure ChunkWire (checked : ListFile.Checked) (ordinal : Nat) (chunk : Chunk) : Prop where
  origin : ListFile.ChunkFrameWire checked ordinal chunk.framed 1
  order : chunk.framed.frames = chunk.dictionary :: chunk.firstData :: chunk.rest
  dictionaryOffset :
    chunk.framed.chunk.metadata.dictionaryPageOffset = some (chunk.dictionary.header.start : Int)
  dataOffset : chunk.framed.chunk.metadata.dataPageOffset = (chunk.firstData.header.start : Int)

abbrev DataWalk := ListFile.Checked → Footer.ColumnChunk → Array Int32 →
  Nat → Budget → State → List Page.Frame → Except GroupError (Budget × State)

abbrev WalkWitness := ListFile.Checked → Footer.ColumnChunk → Array Int32 →
  List Page.Frame → List (List Event) → Prop

def readGroupWith (limits : Limits) (walk : DataWalk) (checked : ListFile.Checked) (ordinal expanded : Nat) :
    Except GroupError (List Row × Nat) := do
  let selected ← selectChunk checked ordinal
  let column := selected.framed.chunk
  let slots := column.metadata.numValues.toNat
  let expectedRows := selected.framed.group.numRows.toNat
  if limits.snappy.parquet.maxGroupSlots < slots then return ← throw .slotLimit
  if checked.limits.page.maxRows < expectedRows then return ← throw .rowLimit
  let dictionary := selected.dictionary
  let entries ← (readEntries limits checked expanded dictionary).mapError (.frame 0 dictionary.header.start)
  let budget : Budget := ⟨slots, expanded - dictionary.value.uncompressedSize⟩
  let (left, state) ← walk checked column entries.toArray 1 budget State.empty
    (selected.firstData :: selected.rest)
  if left.slots ≠ 0 then return ← throw (.missingSlots left.slots)
  let rows := state.finish
  if rows.length ≠ expectedRows then return ← throw (.rowCount expectedRows rows.length)
  pure (rows, left.expanded)

def readGroupUsing (limits : Limits) (read : DataReader) :=
  readGroupWith limits (fun checked column entries => readFramesUsing (read checked column entries))

def readGroup (limits : Limits) (checked : ListFile.Checked) (ordinal expanded : Nat) :
    Except GroupError (List Row × Nat) :=
  readGroupUsing limits (readFrame limits) checked ordinal expanded

abbrev GroupWireWith (limits : Limits) (witness : WalkWitness) (checked : ListFile.Checked) (ordinal : Nat)
    (rows : List Row) (spent : Nat) : Prop :=
  ∃ chunk entries pages,
    ChunkWire checked ordinal chunk ∧ DictionaryWire limits checked chunk.dictionary entries ∧
    witness checked chunk.framed.chunk entries.toArray
      (chunk.firstData :: chunk.rest) pages ∧
    pages.flatten.length = chunk.framed.chunk.metadata.numValues.toNat ∧
    rows.length = chunk.framed.group.numRows.toNat ∧
    ListPage.reconstruct pages.flatten = .ok rows ∧
    rows.flatMap ListPage.rowEvents = pages.flatten ∧
    chunk.framed.chunk.metadata.numValues.toNat ≤ limits.snappy.parquet.maxGroupSlots ∧
    chunk.framed.group.numRows.toNat ≤ checked.limits.page.maxRows ∧
    Snappy.expandedSize chunk.framed.frames = spent

abbrev GroupWireData (limits : Limits) (witness : DataWitness) :=
  GroupWireWith limits (fun checked column entries => List.Forall₂ (witness checked column entries))

structure GroupWireUsing (limits : Limits) (witness : DataWitness) (checked : ListFile.Checked) (ordinal : Nat)
    (rows : List Row) (spent : Nat) : Prop where
  data : GroupWireData limits witness checked ordinal rows spent

structure GroupWire (limits : Limits) (checked : ListFile.Checked) (ordinal : Nat)
    (rows : List Row) (spent : Nat) : Prop where
  data : GroupWireData limits (FrameWire limits) checked ordinal rows spent

def convert (limits : Limits) (source : Bytes) : Snappy.ResultWith SourceError Error :=
  Snappy.convertWith errors limits.snappy (readGroup limits) source

abbrev Readback (limits : Limits) (source : Bytes) (wire : KBytes) :=
  Snappy.ReadbackWith errors limits.snappy (readGroup limits) (GroupWire limits) source wire

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1
