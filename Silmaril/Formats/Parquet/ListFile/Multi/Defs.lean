module

public import Silmaril.Formats.Parquet.ListFile.Defs

/-! Opt-in continuation across complete, uncompressed PLAIN V1 frames of
one checked canonical INT32 LIST column. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.Multi

open Silmaril.Relational
open ListPage (Event State Row)

structure Limits where
  file : ListFile.Limits := {}
  maxGroupSlots : Nat := 1024 * 1024

inductive FrameError where
  | slotBudget (remaining actual : Nat)
  | bodyLimit
  | payloadBounds
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

/-- A leading continuation starts inside an existing list, away from a row boundary. -/
def startsWithinRow : List Event → Bool
  | .next _ :: _ => true
  | _ => false

def readFrame (checked : ListFile.Checked) (column : Footer.ColumnChunk) (remaining : Nat)
    (frame : Page.Frame) : Except FrameError (List Event) := do
  let .dataV1 info := frame.value.kind | throw (.page .pageKind)
  if remaining < info.numValues then return ← throw (.slotBudget remaining info.numValues)
  if checked.limits.page.maxBodyBytes < frame.value.compressedSize then return ← throw .bodyLimit
  let some body := checked.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) |
    throw .payloadBounds
  let events ← (ListPage.decodeV1Events checked.limits.page column.metadata.codec frame.value body).mapError .page
  if column.offsetIndexOffset.isSome && startsWithinRow events then return ← throw .indexedContinuation
  pure events

structure FrameWire (checked : ListFile.Checked) (column : Footer.ColumnChunk) (frame : Page.Frame)
    (events : List Event) : Prop where
  data : ∃ body info,
    checked.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some body ∧
    ListPage.V1Wire column.metadata.codec frame.value body info ∧
    ListPage.EventsWire checked.limits.page info.numValues body events
  indexBoundary : column.offsetIndexOffset.isSome = true → startsWithinRow events = false

abbrev SlotFrameReader (error : Type) := Nat → Page.Frame → Except error (List Event)

/-- Use the original frame order and keep the current list open. Both
decoder and stitching refusals retain the original frame coordinates. -/
def readFramesWith {frameError groupError : Type}
    (indexed : Nat → Nat → frameError → groupError)
    (feedError : ListPage.Error → frameError) (read : SlotFrameReader frameError)
    (frames : List Page.Frame) (ordinal remaining : Nat) (state : State) :
    Except groupError (Nat × State) :=
  match frames with
  | [] => .ok (remaining, state)
  | frame :: rest => do
    let events ← (read remaining frame).mapError (indexed ordinal frame.header.start)
    let next ← (state.feed events).mapError (indexed ordinal frame.header.start ∘ feedError)
    readFramesWith indexed feedError read rest (ordinal + 1) (remaining - events.length) next

def readFrames (checked : ListFile.Checked) (column : Footer.ColumnChunk) :=
  readFramesWith GroupError.frame FrameError.page (readFrame checked column)

/-- The full chunk is framed before decoding and checked against both footer
totals. The group always starts with no live list. -/
def readGroup (maxGroupSlots : Nat) (checked : ListFile.Checked) (ordinal : Nat) :
    Except GroupError (List Row) := do
  let framed ← (checked.frameGroup ordinal).mapError .framing
  let slotCount := framed.chunk.metadata.numValues.toNat
  let rowCount := framed.group.numRows.toNat
  if maxGroupSlots < slotCount then return ← throw .slotLimit
  if checked.limits.page.maxRows < rowCount then return ← throw .rowLimit
  let (remaining, state) ← readFrames checked framed.chunk framed.frames 0 slotCount State.empty
  if remaining ≠ 0 then return ← throw (.missingSlots remaining)
  let rows := state.finish
  if rows.length ≠ rowCount then return ← throw (.rowCount rowCount rows.length)
  pure rows

structure GroupWire (maxGroupSlots : Nat) (checked : ListFile.Checked) (ordinal : Nat) (slots : List Row) : Prop where
  data : ∃ (framed : ListFile.FramedGroup) (pages : List (List Event)),
    ListFile.FramedGroupWire checked ordinal framed ∧
    List.Forall₂ (FrameWire checked framed.chunk) framed.frames pages ∧
    pages.flatten.length = framed.chunk.metadata.numValues.toNat ∧
    slots.length = framed.group.numRows.toNat ∧
    slots.flatMap ListPage.rowEvents = pages.flatten ∧
    framed.chunk.metadata.numValues.toNat ≤ maxGroupSlots ∧
    framed.group.numRows.toNat ≤ checked.limits.page.maxRows

inductive Error where
  | openFailure (cause : ListFile.OpenError)
  | groupFailure (ordinal : Nat) (cause : GroupError)
  deriving DecidableEq, Repr

def groupSource (limits : Limits) (checked : ListFile.Checked) :
    Reader.Source Nat (ListFile.schema checked) ListFile.Cell Error :=
  ⟨List.range checked.snapshot.groupCount,
    fun index => ((readGroup limits.maxGroupSlots checked index).mapError (.groupFailure index)).map (ListFile.rows checked),
    fun _ => .ok ()⟩

def openSource (limits : Limits) (source : Bytes) : Reader.OpenResult Nat String ListFile.Cell Error :=
  ((ListFile.openFile limits.file source).mapError .openFailure).map fun checked =>
    ⟨ListFile.schema checked, groupSource limits checked⟩

def readAll (limits : Limits) (source : Bytes) : Arrow.Events.EventStream String ListFile.Cell Error :=
  Reader.readAll (openSource limits source)

end Silmaril.Formats.Parquet.ListFile.Multi
