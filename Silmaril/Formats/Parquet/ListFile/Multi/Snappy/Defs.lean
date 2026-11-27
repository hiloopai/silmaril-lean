module

public import Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Defs
public import Silmaril.Formats.Parquet.Page.Checksum.Defs
public import Silmaril.Formats.Parquet.Payload.Defs

/-! Opt-in native LIST reading for Snappy-compressed PLAIN V1 pages. -/

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

/-- Continue the open list through the original ordered frames. -/
def readFrames (limits : Limits) (checked : ListFile.Checked) (column : Footer.ColumnChunk)
    (ordinal : Nat) (budget : Budget) (state : State) :
    List Page.Frame → Except GroupError (Budget × State)
  | [] => .ok (budget, state)
  | frame :: rest => do
    let events ← (readFrame limits checked column budget frame).mapError (.frame ordinal frame.header.start)
    let next ← (state.feed events).mapError (.frame ordinal frame.header.start ∘ .page)
    readFrames limits checked column (ordinal + 1) (budget.use frame events) next rest

def expandedSize (frames : List Page.Frame) : Nat :=
  (frames.map (·.value.uncompressedSize)).sum

def readGroup (limits : Limits) (checked : ListFile.Checked) (ordinal expanded : Nat) :
    Except GroupError (List Row × Nat) := do
  let framed ← (checked.frameGroupFor 1 ordinal).mapError .framing
  let slotCount := framed.chunk.metadata.numValues.toNat
  let rowCount := framed.group.numRows.toNat
  if limits.parquet.maxGroupSlots < slotCount then return ← throw .slotLimit
  if checked.limits.page.maxRows < rowCount then return ← throw .rowLimit
  let (left, state) ← readFrames limits checked framed.chunk 0 ⟨slotCount, expanded⟩ State.empty framed.frames
  if left.slots ≠ 0 then return ← throw (.missingSlots left.slots)
  let rows := state.finish
  if rows.length ≠ rowCount then return ← throw (.rowCount rowCount rows.length)
  pure (rows, left.expanded)

structure GroupWire (limits : Limits) (checked : ListFile.Checked) (ordinal : Nat)
    (rows : List Row) (spent : Nat) : Prop where
  data : ∃ framed pages,
    ListFile.FramedGroupWire checked ordinal framed 1 ∧
    List.Forall₂ (FrameWire limits checked framed.chunk) framed.frames pages ∧
    pages.flatten.length = framed.chunk.metadata.numValues.toNat ∧
    rows.length = framed.group.numRows.toNat ∧
    ListPage.reconstruct pages.flatten = .ok rows ∧
    rows.flatMap ListPage.rowEvents = pages.flatten ∧
    framed.chunk.metadata.numValues.toNat ≤ limits.parquet.maxGroupSlots ∧
    framed.group.numRows.toNat ≤ checked.limits.page.maxRows ∧
    expandedSize framed.frames = spent

/-- Preserve the successful groups before the first indexed failure. A single
expansion budget is threaded through the whole file. -/
def readGroups (limits : Limits) (checked : ListFile.Checked) (expanded : Nat) :
    List Nat → List (List Row) × Except SourceError Nat
  | [] => ([], .ok expanded)
  | ordinal :: rest =>
    match readGroup limits checked ordinal expanded with
    | .error cause => ([], .error (.groupFailure ordinal cause))
    | .ok (rows, left) =>
      let (groups, outcome) := readGroups limits checked left rest
      (rows :: groups, outcome)

abbrev SourceTrace := Arrow.Events.EventStream String ListFile.Cell SourceError

inductive Error where
  | source (cause : SourceError)
  | writer (cause : Arrow.ListInt32.Stream.Writer.Error)
  deriving DecidableEq, Repr

structure Result where
  trace : SourceTrace
  wire : Except Error KBytes

def convert (limits : Limits) (source : Bytes) : Result :=
  match ListFile.openFile limits.parquet.file source with
  | .error cause => ⟨.error (.openFailure cause), .error (.source (.openFailure cause))⟩
  | .ok checked =>
    let (groups, outcome) := readGroups limits checked limits.maxExpandedBytes (List.range checked.snapshot.groupCount)
    let batches := groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked)
    match outcome with
    | .error cause => ⟨.ok ⟨ListFile.schema checked, ⟨batches, .readError cause⟩⟩, .error (.source cause)⟩
    | .ok _ => ⟨.ok ⟨ListFile.schema checked, ⟨batches, .eos⟩⟩,
      (Arrow.ListInt32.Stream.Writer.emit limits.ipc (ToIpc.fieldOf checked) groups).mapError .writer⟩

structure Readback (limits : Limits) (source : Bytes) (wire : KBytes) : Prop where
  data : ∃ checked groups costs left decoded size,
    ListFile.openFile limits.parquet.file source = .ok checked ∧
    ListFile.OpenWire limits.parquet.file source checked ∧
    readGroups limits checked limits.maxExpandedBytes (List.range checked.snapshot.groupCount) =
      (groups, .ok left) ∧
    List.Forall₂ (fun ordinal (batch : List Row × Nat) => GroupWire limits checked ordinal batch.1 batch.2)
      (List.range checked.snapshot.groupCount) (groups.zip costs) ∧
    costs.length = groups.length ∧ costs.sum + left = limits.maxExpandedBytes ∧
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .eos⟩⟩ ∧
    Arrow.ListInt32.Stream.read limits.ipc wire = .ok decoded ∧
    Arrow.ListInt32.Stream.Writer.Agrees (ToIpc.fieldOf checked) groups decoded ∧
    wire.wf = true ∧
    Arrow.readEnvelope limits.ipc.ipc wire 0 = .ok (.metadata size) ∧
    Arrow.ListInt32.readSchema limits.ipc.ipc (wire.slice 8 size) = .ok (ToIpc.fieldOf checked) ∧
    Arrow.ListInt32.Stream.BatchesWire limits.ipc wire limits.ipc.ipc.batches 0 0 (8 + size) decoded.batches

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy
