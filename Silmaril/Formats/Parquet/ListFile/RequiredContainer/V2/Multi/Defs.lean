module

public import Silmaril.Formats.Parquet.ListFile.Multi.Defs
public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Defs

/-! Opt-in uncompressed PLAIN V2 required LIST of nullable INT32. Each
nonempty page starts at a row boundary. The original chunk is read in order. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi

open ListPage (Event Row State)
open Silmaril.Relational
open RequiredContainer (Checked SectionsWire)

structure Limits extends RequiredContainer.Limits where
  maxGroupSlots : Nat := 1024 * 1024

inductive FrameError where
  | data (cause : V2.FrameError)
  | slotBudget (remaining actual : Nat)
  | rowContinuation
  deriving DecidableEq, Repr

inductive GroupError where
  | framing (cause : ListFile.ReadError)
  | slotLimit
  | rowLimit
  | missingSlots (count : Nat)
  | rowCount (expected actual : Nat)
  | frame (ordinal offset : Nat) (cause : FrameError)
  deriving DecidableEq, Repr

/-- Called on an original frame from the admitted codec-zero chunk. -/
def readFrame (checked : Checked) (remaining : Nat) (frame : Page.Frame) :
    Except FrameError (List Event) := do
  let .dataV2 info := frame.value.kind | throw (.data (.page .pageKind))
  if frame.value.crc.isSome then return ← throw (.data (.page .crc))
  if info.encoding ≠ 0 then return ← throw (.data (.page .encoding))
  if remaining < info.numValues then return ← throw (.slotBudget remaining info.numValues)
  if checked.limits.page.maxRows < info.numRows then return ← throw (.data (.page .rowLimit))
  let sections ← (readSections checked.limits.page checked.snapshot.bytes frame info).mapError .data
  let events ← (RequiredContainer.decodeSections checked.limits.page info.numValues sections.repetition
    sections.definition sections.scalars).mapError (.data ∘ .page)
  if ListFile.Multi.startsWithinRow events then return ← throw .rowContinuation
  let absent := missingSlots events
  if absent ≠ info.numNulls then return ← throw (.data (.pageNulls info.numNulls absent))
  let starts := rowStarts events
  if starts ≠ info.numRows then return ← throw (.data (.pageRows info.numRows starts))
  pure events

structure FrameWire (checked : Checked) (frame : Page.Frame) (events : List Event) : Prop where
  data : ∃ info sections,
    frame.value.kind = .dataV2 info ∧ frame.value.crc = none ∧ info.encoding = 0 ∧
    RawWire checked.limits.page checked.snapshot.bytes frame info sections ∧
    SectionsWire info.numValues sections.repetition sections.definition sections.scalars events ∧
    events.length = info.numValues ∧ rowStarts events = info.numRows ∧
    missingSlots events = info.numNulls ∧ info.numRows ≤ checked.limits.page.maxRows
  boundary : ListFile.Multi.startsWithinRow events = false

def readFrames (checked : Checked) :=
  ListFile.Multi.readFramesWith GroupError.frame (FrameError.data ∘ V2.FrameError.page) (readFrame checked)

def readGroup (maxGroupSlots : Nat) : RequiredContainer.GroupReader GroupError := fun checked ordinal => do
  let framed ← (checked.frameGroup ordinal).mapError .framing
  let slots := framed.chunk.metadata.numValues.toNat
  let rows := framed.group.numRows.toNat
  if maxGroupSlots < slots then return ← throw .slotLimit
  if checked.limits.page.maxRows < rows then return ← throw .rowLimit
  let (remaining, state) ← readFrames checked framed.frames 0 slots State.empty
  if remaining ≠ 0 then return ← throw (.missingSlots remaining)
  let output := state.finish
  if output.length ≠ rows then return ← throw (.rowCount rows output.length)
  pure output

structure GroupWire (maxGroupSlots : Nat) (checked : Checked) (ordinal : Nat) (rows : List Row) : Prop where
  parents : ∀ row ∈ rows, row.isSome = true
  data : ∃ (framed : ListFile.FramedGroup) (pages : List (List Event)) (headers : List Page.DataV2),
    ListFile.FramedGroupWire checked ordinal framed ∧
    List.Forall₂ (FrameWire checked) framed.frames pages ∧
    List.Forall₂ (fun (frame : Page.Frame) header => frame.value.kind = .dataV2 header) framed.frames headers ∧
    ListPage.reconstruct pages.flatten = .ok rows ∧
    rows.flatMap ListPage.rowEvents = pages.flatten ∧
    (headers.map (·.numValues)).sum = framed.chunk.metadata.numValues.toNat ∧
    (headers.map (·.numRows)).sum = rows.length ∧ rows.length = framed.group.numRows.toNat ∧
    (headers.map (·.numNulls)).sum = missingSlots (rows.flatMap ListPage.rowEvents) ∧
    framed.chunk.metadata.numValues.toNat ≤ maxGroupSlots ∧
    framed.group.numRows.toNat ≤ checked.limits.page.maxRows

abbrev Result := RequiredContainer.Result GroupError

def convert (limits : Limits) (source : Bytes) : Result :=
  RequiredContainer.convertUsing (readGroup limits.maxGroupSlots) limits.toLimits source

abbrev Readback (limits : Limits) :=
  RequiredContainer.ReadbackUsing (readGroup limits.maxGroupSlots) (GroupWire limits.maxGroupSlots) limits.toLimits

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi
