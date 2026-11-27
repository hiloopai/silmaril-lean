module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Defs

/-! Select the original V1 or V2 LIST decoder independently for each frame. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed

open ListPage (Event State Row)

def readFrame (limits : Limits) (checked : ListFile.Checked) (column : Footer.ColumnChunk)
    (budget : Budget) (frame : Page.Frame) : Except FrameError (List Event) :=
  match frame.value.kind with
  | .dataV1 _ => Snappy.readFrame limits checked column budget frame
  | .dataV2 _ => readV2Frame limits checked budget frame
  | _ => .error (.page .pageKind)

def FrameWire (limits : Limits) (checked : ListFile.Checked) (column : Footer.ColumnChunk)
    (frame : Page.Frame) (events : List Event) : Prop :=
  match frame.value.kind with
  | .dataV1 _ => Snappy.FrameWire limits checked column frame events
  | .dataV2 _ => V2FrameWire limits checked frame events
  | _ => False

def frameSlots (frame : Page.Frame) : Nat :=
  match frame.value.kind with
  | .dataV1 info => info.numValues
  | .dataV2 info => info.numValues
  | _ => 0

/-- A V2 frame requires a row boundary at its end. Empty V1 frames preserve
that requirement until the next nonempty page. -/
def nextBoundary (pending : Bool) (frame : Page.Frame) : Bool :=
  match frame.value.kind with
  | .dataV2 _ => true
  | .dataV1 info => pending && info.numValues == 0
  | _ => pending

inductive Boundaries : Bool → List Page.Frame → List (List Event) → Prop where
  | nil (pending : Bool) : Boundaries pending [] []
  | cons {pending : Bool} {frame : Page.Frame} {frames : List Page.Frame}
      {events : List Event} {pages : List (List Event)}
      (start : pending = true → Multi.startsWithinRow events = false)
      (rest : Boundaries (nextBoundary pending frame) frames pages) :
      Boundaries pending (frame :: frames) (events :: pages)

def readFrames (limits : Limits) (checked : ListFile.Checked) (column : Footer.ColumnChunk)
    (ordinal : Nat) (pending : Bool) (budget : Budget) (state : State) :
    List Page.Frame → Except GroupError (Budget × State)
  | [] => .ok (budget, state)
  | frame :: rest => do
    let events ← (readFrame limits checked column budget frame).mapError (.frame ordinal frame.header.start)
    if pending && Multi.startsWithinRow events then
      return ← throw (.frame ordinal frame.header.start .v2Continuation)
    let next ← (state.feed events).mapError (.frame ordinal frame.header.start ∘ .page)
    readFrames limits checked column (ordinal + 1) (nextBoundary pending frame) (budget.use frame events) next rest

def readGroup (limits : Limits) (checked : ListFile.Checked) (ordinal expanded : Nat) :
    Except GroupError (List Row × Nat) :=
  readGroupUsing limits checked (fun column budget => readFrames limits checked column 0 false budget State.empty)
    ordinal expanded

structure GroupWire (limits : Limits) (checked : ListFile.Checked) (ordinal : Nat)
    (rows : List Row) (spent : Nat) : Prop where
  data : ∃ framed pages,
    ListFile.FramedGroupWire checked ordinal framed 1 ∧
    List.Forall₂ (FrameWire limits checked framed.chunk) framed.frames pages ∧
    Boundaries false framed.frames pages ∧
    pages.flatten.length = framed.chunk.metadata.numValues.toNat ∧
    (framed.frames.map frameSlots).sum = framed.chunk.metadata.numValues.toNat ∧
    rows.length = framed.group.numRows.toNat ∧
    ListPage.reconstruct pages.flatten = .ok rows ∧
    rows.flatMap ListPage.rowEvents = pages.flatten ∧
    framed.chunk.metadata.numValues.toNat ≤ limits.parquet.maxGroupSlots ∧
    framed.group.numRows.toNat ≤ checked.limits.page.maxRows ∧
    expandedSize framed.frames = spent

def convert (limits : Limits) (source : Bytes) : Result :=
  convertUsing limits (readGroup limits) source

abbrev Readback (limits : Limits) (source : Bytes) (wire : KBytes) :=
  ReadbackUsing limits (readGroup limits) (GroupWire limits) source wire

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Mixed
