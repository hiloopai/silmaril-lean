module

public import Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Defs
public import Silmaril.Formats.Parquet.Page.Checksum.Defs
public import Silmaril.Formats.Parquet.Payload.Defs

/-! Opt-in native LIST reading for a selected Snappy PLAIN data page version. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy

open Silmaril.Relational
open ListPage (Event State Row)

structure Limits where
  parquet : Multi.Limits := {}
  maxStoredPageBytes : Nat := 16 * 1024 * 1024
  /-- Total expanded body bytes across all frames of all groups. -/
  maxExpandedBytes : Nat := 64 * 1024 * 1024
  ipc : Arrow.ListInt32.Stream.Limits := {}

inductive FrameError where
  | slotBudget (remaining actual : Nat)
  | expandedBudget (remaining actual : Nat)
  | checksum (cause : Page.Checksum.Error)
  | payload (cause : Payload.Error)
  | indexedContinuation
  | v2LevelExtent
  | v2LevelLimit
  | v2Continuation
  | v2RowCount (expected actual : Nat)
  | v2NullCount (expected actual : Nat)
  | page (cause : ListPage.Error)
  deriving DecidableEq, Repr

inductive GroupError where
  | framing (cause : ListFile.ReadError)
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

structure Budget where
  slots : Nat
  expanded : Nat

def Budget.use (budget : Budget) (frame : Page.Frame) (events : List Event) : Budget :=
  ⟨budget.slots - events.length, budget.expanded - frame.value.uncompressedSize⟩

def bounds (limits : Limits) (checked : ListFile.Checked) (budget : Budget)
    (frame : Page.Frame) : Payload.Bounds :=
  ⟨frame.value.compressedSize, limits.maxStoredPageBytes, frame.value.uncompressedSize,
    min checked.limits.page.maxBodyBytes budget.expanded, 0⟩

/-- Validate the stored payload on the original snapshot before expansion.
For V1 the raw Snappy member covers both level sections and the scalar suffix. -/
def readFrame (limits : Limits) (checked : ListFile.Checked) (column : Footer.ColumnChunk)
    (budget : Budget) (frame : Page.Frame) : Except FrameError (List Event) := do
  let .dataV1 info := frame.value.kind | throw (.page .pageKind)
  if ¬ (info.encoding = 0 ∧ info.repetitionLevelEncoding = 3 ∧ info.definitionLevelEncoding = 3) then
    return ← throw (.page .encoding)
  if budget.slots < info.numValues then return ← throw (.slotBudget budget.slots info.numValues)
  if budget.expanded < frame.value.uncompressedSize then
    return ← throw (.expandedBudget budget.expanded frame.value.uncompressedSize)
  let source := checked.snapshot.bytes
  let _ ← (Page.Checksum.verify limits.maxStoredPageBytes source frame).mapError .checksum
  let stored := Page.Checksum.payloadBytes source frame
  let output ← (Payload.decode (bounds limits checked budget frame) 1 stored.toList).mapError .payload
  let events ← (ListPage.decodeEvents checked.limits.page info.numValues (Bytes.ofList output)).mapError .page
  if column.offsetIndexOffset.isSome && Multi.startsWithinRow events then return ← throw .indexedContinuation
  pure events

structure FrameWire (limits : Limits) (checked : ListFile.Checked) (column : Footer.ColumnChunk)
    (frame : Page.Frame) (events : List Event) : Prop where
  data : ∃ status stored expanded info,
    Page.Checksum.verify limits.maxStoredPageBytes checked.snapshot.bytes frame = .ok status ∧
    checked.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.maxStoredPageBytes ∧
    Payload.Decodes frame.value.uncompressedSize .snappy stored.toList expanded.toList ∧
    expanded.length = frame.value.uncompressedSize ∧
    frame.value.kind = .dataV1 info ∧
    (info.encoding = 0 ∧ info.repetitionLevelEncoding = 3 ∧ info.definitionLevelEncoding = 3) ∧
    ListPage.EventsWire checked.limits.page info.numValues expanded events
  indexBoundary : column.offsetIndexOffset.isSome = true → Multi.startsWithinRow events = false

inductive PageVersion where
  | v1 | v2

structure V2Sections where
  repetition : Bytes
  definition : Bytes
  scalars : Bytes

def v2LevelBytes (info : Page.DataV2) : Nat :=
  info.repetitionBytes + info.definitionBytes

def v2Codec (info : Page.DataV2) : Int :=
  if info.isCompressed then 1 else 0

def v2Bounds {container : ListFile.Container} (limits : Limits) (checked : ListFile.Checked container)
    (frame : Page.Frame) (info : Page.DataV2) : Payload.Bounds :=
  let levels := v2LevelBytes info
  ⟨frame.value.compressedSize - levels, limits.maxStoredPageBytes,
    frame.value.uncompressedSize - levels, checked.limits.page.maxBodyBytes - levels, 0⟩

/-- The two level slices are stored raw. Only the scalar suffix uses the
resolved compression flag. The complete body contributes to the caps. -/
def prepareV2 {container : ListFile.Container} (limits : Limits) (checked : ListFile.Checked container)
    (frame : Page.Frame) (info : Page.DataV2) (stored : Bytes) : Except FrameError V2Sections := do
  let levels := v2LevelBytes info
  if stored.length ≠ frame.value.compressedSize ∨ frame.value.compressedSize < levels ∨
      frame.value.uncompressedSize < levels then return ← throw .v2LevelExtent
  if checked.limits.page.levels.bytes < info.repetitionBytes ∨
      checked.limits.page.levels.bytes < info.definitionBytes then return ← throw .v2LevelLimit
  if checked.limits.page.maxBodyBytes < frame.value.uncompressedSize then
    return ← throw (.payload .outputLimit)
  let bytes := stored.toList
  let afterRep := bytes.drop info.repetitionBytes
  let output ← (Payload.decode (v2Bounds limits checked frame info)
    (v2Codec info) (afterRep.drop info.definitionBytes)).mapError .payload
  pure ⟨Bytes.ofList (bytes.take info.repetitionBytes), Bytes.ofList (afterRep.take info.definitionBytes),
    Bytes.ofList output⟩

def pageRows (events : List Event) : Nat :=
  events.countP (fun event => event.wire.1 == 0)

def pageNulls (events : List Event) : Nat :=
  events.countP (fun event => event.wire.2.2.isNone)

/-- V2 pages always start at a row boundary, even when the group has an open
list from the preceding page. Null counts include every nonphysical slot. -/
def checkV2Counts (info : Page.DataV2) (events : List Event) : Except FrameError Unit := do
  if Multi.startsWithinRow events then return ← throw .v2Continuation
  if pageRows events ≠ info.numRows then return ← throw (.v2RowCount info.numRows (pageRows events))
  if pageNulls events ≠ info.numNulls then return ← throw (.v2NullCount info.numNulls (pageNulls events))

def readV2Frame (limits : Limits) (checked : ListFile.Checked)
    (budget : Budget) (frame : Page.Frame) : Except FrameError (List Event) := do
  let .dataV2 info := frame.value.kind | throw (.page .pageKind)
  if info.encoding ≠ 0 then return ← throw (.page .encoding)
  if budget.slots < info.numValues then return ← throw (.slotBudget budget.slots info.numValues)
  if budget.expanded < frame.value.uncompressedSize then
    return ← throw (.expandedBudget budget.expanded frame.value.uncompressedSize)
  let source := checked.snapshot.bytes
  let _ ← (Page.Checksum.verify limits.maxStoredPageBytes source frame).mapError .checksum
  let sections ← prepareV2 limits checked frame info (Page.Checksum.payloadBytes source frame)
  let events ← (ListPage.decodeSections checked.limits.page info.numValues
    sections.repetition sections.definition sections.scalars).mapError .page
  checkV2Counts info events
  pure events

structure V2BodyWire {container : ListFile.Container} (checked : ListFile.Checked container) (frame : Page.Frame) (info : Page.DataV2)
    (stored : Bytes) (sections : V2Sections) : Prop where
  repetitionSize : sections.repetition.length = info.repetitionBytes
  definitionSize : sections.definition.length = info.definitionBytes
  repLimit : info.repetitionBytes ≤ checked.limits.page.levels.bytes
  defLimit : info.definitionBytes ≤ checked.limits.page.levels.bytes
  expandedCap : frame.value.uncompressedSize ≤ checked.limits.page.maxBodyBytes
  exact : ∃ suffix codec,
    stored.toList = sections.repetition.toList ++ sections.definition.toList ++ suffix ∧
    suffix.length = frame.value.compressedSize - v2LevelBytes info ∧
    sections.scalars.length = frame.value.uncompressedSize - v2LevelBytes info ∧
    v2LevelBytes info + sections.scalars.length = frame.value.uncompressedSize ∧
    Payload.Codec.ofId (v2Codec info) = some codec ∧
    Payload.Decodes (frame.value.uncompressedSize - v2LevelBytes info) codec suffix sections.scalars.toList

structure V2FrameWire (limits : Limits) (checked : ListFile.Checked) (frame : Page.Frame)
    (events : List Event) : Prop where
  data : ∃ status stored info sections,
    Page.Checksum.verify limits.maxStoredPageBytes checked.snapshot.bytes frame = .ok status ∧
    checked.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.maxStoredPageBytes ∧
    frame.value.kind = .dataV2 info ∧ info.encoding = 0 ∧
    V2BodyWire checked frame info stored sections ∧
    ListPage.SectionsWire info.numValues sections.repetition sections.definition sections.scalars events ∧
    Multi.startsWithinRow events = false ∧ pageRows events = info.numRows ∧
    pageNulls events = info.numNulls ∧ sections.scalars.length = 4 * (info.numValues - info.numNulls)

def readFrameFor (version : PageVersion) (limits : Limits) (checked : ListFile.Checked)
    (column : Footer.ColumnChunk) (budget : Budget) (frame : Page.Frame) : Except FrameError (List Event) :=
  match version with
  | .v1 => readFrame limits checked column budget frame
  | .v2 => readV2Frame limits checked budget frame

def FrameWireFor (version : PageVersion) (limits : Limits) (checked : ListFile.Checked)
    (column : Footer.ColumnChunk) (frame : Page.Frame) (events : List Event) : Prop :=
  match version with
  | .v1 => FrameWire limits checked column frame events
  | .v2 => V2FrameWire limits checked frame events

/-- Continue the open list through the original ordered frames. -/
def readFramesFor (version : PageVersion) (limits : Limits) (checked : ListFile.Checked) (column : Footer.ColumnChunk)
    (ordinal : Nat) (budget : Budget) (state : State) :
    List Page.Frame → Except GroupError (Budget × State)
  | [] => .ok (budget, state)
  | frame :: rest => do
    let events ← (readFrameFor version limits checked column budget frame).mapError (.frame ordinal frame.header.start)
    let next ← (state.feed events).mapError (.frame ordinal frame.header.start ∘ .page)
    readFramesFor version limits checked column (ordinal + 1) (budget.use frame events) next rest

def readFrames (limits : Limits) (checked : ListFile.Checked) (column : Footer.ColumnChunk)
    (ordinal : Nat) (budget : Budget) (state : State) (frames : List Page.Frame) :
    Except GroupError (Budget × State) :=
  readFramesFor .v1 limits checked column ordinal budget state frames

def expandedSize (frames : List Page.Frame) : Nat :=
  (frames.map (·.value.uncompressedSize)).sum

abbrev GroupWalk :=
  Footer.ColumnChunk → Budget → List Page.Frame → Except GroupError (Budget × State)

/-- Enforce the group counts and budgets on the selected original frames. -/
def readFramedGroupUsing (limits : Limits) (checked : ListFile.Checked) (walk : GroupWalk)
    (framed : ListFile.FramedGroup) (expanded : Nat) : Except GroupError (List Row × Nat) := do
  let slotCount := framed.chunk.metadata.numValues.toNat
  let rowCount := framed.group.numRows.toNat
  if limits.parquet.maxGroupSlots < slotCount then return ← throw .slotLimit
  if checked.limits.page.maxRows < rowCount then return ← throw .rowLimit
  let (left, state) ← walk framed.chunk ⟨slotCount, expanded⟩ framed.frames
  if left.slots ≠ 0 then return ← throw (.missingSlots left.slots)
  let rows := state.finish
  if rows.length ≠ rowCount then return ← throw (.rowCount rowCount rows.length)
  pure (rows, left.expanded)

/-- Frame the original non-dictionary column and enforce the shared group counts. -/
def readGroupUsing (limits : Limits) (checked : ListFile.Checked) (walk : GroupWalk)
    (ordinal expanded : Nat) : Except GroupError (List Row × Nat) := do
  let framed ← (checked.frameGroupFor 1 ordinal).mapError .framing
  readFramedGroupUsing limits checked walk framed expanded

def readFramedGroupFor (version : PageVersion) (limits : Limits) (checked : ListFile.Checked)
    (framed : ListFile.FramedGroup) (expanded : Nat) : Except GroupError (List Row × Nat) :=
  readFramedGroupUsing limits checked
    (fun column budget => readFramesFor version limits checked column 0 budget State.empty) framed expanded

def readGroupFor (version : PageVersion) (limits : Limits) (checked : ListFile.Checked)
    (ordinal expanded : Nat) : Except GroupError (List Row × Nat) :=
  readGroupUsing limits checked (fun column budget => readFramesFor version limits checked column 0 budget State.empty)
    ordinal expanded

def readGroup (limits : Limits) (checked : ListFile.Checked) (ordinal expanded : Nat) :
    Except GroupError (List Row × Nat) :=
  readGroupFor .v1 limits checked ordinal expanded

structure GroupWire (limits : Limits) (checked : ListFile.Checked) (ordinal : Nat)
    (rows : List Row) (spent : Nat) (version : PageVersion := .v1) : Prop where
  data : ∃ framed pages,
    ListFile.FramedGroupWire checked ordinal framed 1 ∧
    List.Forall₂ (FrameWireFor version limits checked framed.chunk) framed.frames pages ∧
    pages.flatten.length = framed.chunk.metadata.numValues.toNat ∧
    rows.length = framed.group.numRows.toNat ∧
    ListPage.reconstruct pages.flatten = .ok rows ∧
    rows.flatMap ListPage.rowEvents = pages.flatten ∧
    framed.chunk.metadata.numValues.toNat ≤ limits.parquet.maxGroupSlots ∧
    framed.group.numRows.toNat ≤ checked.limits.page.maxRows ∧
    expandedSize framed.frames = spent

abbrev GroupReaderFor (failure : Type) :=
  ListFile.Checked → Nat → Nat → Except failure (List Row × Nat)

abbrev GroupReader := GroupReaderFor GroupError

/-- Preserve the successful groups before the first indexed failure. A single
expansion budget is threaded through the whole file. -/
def readGroupsWith {ε σ : Type} (wrap : Nat → ε → σ) (read : GroupReaderFor ε)
    (checked : ListFile.Checked) (expanded : Nat) : List Nat → List (List Row) × Except σ Nat
  | [] => ([], .ok expanded)
  | ordinal :: rest =>
    match read checked ordinal expanded with
    | .error cause => ([], .error (wrap ordinal cause))
    | .ok (rows, left) =>
      let (groups, outcome) := readGroupsWith wrap read checked left rest
      (rows :: groups, outcome)

def readGroupsUsing (read : GroupReader) (checked : ListFile.Checked) (expanded : Nat) (indices : List Nat) :
    List (List Row) × Except SourceError Nat :=
  readGroupsWith SourceError.groupFailure read checked expanded indices

def readGroupsFor (version : PageVersion) (limits : Limits) (checked : ListFile.Checked)
    (expanded : Nat) (groups : List Nat) : List (List Row) × Except SourceError Nat :=
  readGroupsUsing (readGroupFor version limits) checked expanded groups

def readGroups (limits : Limits) (checked : ListFile.Checked) (expanded : Nat) (groups : List Nat) :
    List (List Row) × Except SourceError Nat :=
  readGroupsFor .v1 limits checked expanded groups

abbrev SourceTrace := Arrow.Events.EventStream String ListFile.Cell SourceError

inductive Error where
  | source (cause : SourceError)
  | writer (cause : Arrow.ListInt32.Stream.Writer.Error)
  deriving DecidableEq, Repr

structure Result where
  trace : SourceTrace
  wire : Except Error KBytes

structure ConversionErrors (group source output : Type) where
  openFailure : ListFile.OpenError → source
  groupFailure : Nat → group → source
  sourceFailure : source → output
  writerFailure : Arrow.ListInt32.Stream.Writer.Error → output

structure ResultWith (source output : Type) where
  trace : Arrow.Events.EventStream String ListFile.Cell source
  wire : Except output KBytes

def standardErrors : ConversionErrors GroupError SourceError Error :=
  ⟨.openFailure, .groupFailure, .source, .writer⟩

def convertWith {ε σ ρ : Type} (errors : ConversionErrors ε σ ρ) (limits : Limits)
    (read : GroupReaderFor ε) (source : Bytes) : ResultWith σ ρ :=
  match ListFile.openFile limits.parquet.file source with
  | .error cause => ⟨.error (errors.openFailure cause), .error (errors.sourceFailure (errors.openFailure cause))⟩
  | .ok checked =>
    let (groups, outcome) := readGroupsWith errors.groupFailure read checked limits.maxExpandedBytes (List.range checked.snapshot.groupCount)
    let batches := groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked)
    match outcome with
    | .error cause => ⟨.ok ⟨ListFile.schema checked, ⟨batches, .readError cause⟩⟩, .error (errors.sourceFailure cause)⟩
    | .ok _ => ⟨.ok ⟨ListFile.schema checked, ⟨batches, .eos⟩⟩,
      (Arrow.ListInt32.Stream.Writer.emit limits.ipc (ToIpc.fieldOf checked) groups).mapError errors.writerFailure⟩

def convertUsing (limits : Limits) (read : GroupReader) (source : Bytes) : Result :=
  let converted := convertWith standardErrors limits read source
  ⟨converted.trace, converted.wire⟩

def convertFor (version : PageVersion) (limits : Limits) (source : Bytes) : Result :=
  convertUsing limits (readGroupFor version limits) source

def convert (limits : Limits) (source : Bytes) : Result :=
  convertFor .v1 limits source

/-- Select the strict V2 row-boundary profile. -/
def convertV2 (limits : Limits) (source : Bytes) : Result :=
  convertFor .v2 limits source

abbrev ReadbackDataWith {ε σ ρ : Type} (errors : ConversionErrors ε σ ρ) (limits : Limits) (read : GroupReaderFor ε)
    (witness : ListFile.Checked → Nat → List Row → Nat → Prop) (source : Bytes) (wire : KBytes) : Prop :=
  ∃ checked groups costs left decoded size,
    ListFile.openFile limits.parquet.file source = .ok checked ∧
    ListFile.OpenWire limits.parquet.file source checked ∧
    readGroupsWith errors.groupFailure read checked limits.maxExpandedBytes (List.range checked.snapshot.groupCount) =
      (groups, .ok left) ∧
    List.Forall₂ (fun ordinal (batch : List Row × Nat) => witness checked ordinal batch.1 batch.2)
      (List.range checked.snapshot.groupCount) (groups.zip costs) ∧
    costs.length = groups.length ∧ costs.sum + left = limits.maxExpandedBytes ∧
    (convertWith errors limits read source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .eos⟩⟩ ∧
    Arrow.ListInt32.Stream.read limits.ipc wire = .ok decoded ∧
    Arrow.ListInt32.Stream.Writer.Agrees (ToIpc.fieldOf checked) groups decoded ∧
    wire.wf = true ∧
    Arrow.readEnvelope limits.ipc.ipc wire 0 = .ok (.metadata size) ∧
    Arrow.ListInt32.readSchema limits.ipc.ipc (wire.slice 8 size) = .ok (ToIpc.fieldOf checked) ∧
    Arrow.ListInt32.Stream.BatchesWire limits.ipc wire limits.ipc.ipc.batches 0 0 (8 + size) decoded.batches

structure ReadbackWith {ε σ ρ : Type} (errors : ConversionErrors ε σ ρ) (limits : Limits) (read : GroupReaderFor ε)
    (witness : ListFile.Checked → Nat → List Row → Nat → Prop) (source : Bytes) (wire : KBytes) : Prop where
  data : ReadbackDataWith errors limits read witness source wire

structure ReadbackUsing (limits : Limits) (read : GroupReader)
    (witness : ListFile.Checked → Nat → List Row → Nat → Prop) (source : Bytes) (wire : KBytes) : Prop where
  data : ReadbackDataWith standardErrors limits read witness source wire

structure Readback (limits : Limits) (source : Bytes) (wire : KBytes)
    (version : PageVersion := .v1) : Prop where
  data : ReadbackDataWith standardErrors limits (readGroupFor version limits)
    (fun checked ordinal rows spent => GroupWire limits checked ordinal rows spent version) source wire

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy
