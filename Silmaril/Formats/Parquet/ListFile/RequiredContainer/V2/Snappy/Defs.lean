module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Defs
public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Defs

/-! One complete Snappy-column PLAIN Data Page V2 per required LIST group. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy

open ListPage (Event Row)
open RequiredContainer (Checked SectionsWire)

structure Limits extends RequiredContainer.Limits where
  maxStoredPageBytes : Nat := 16 * 1024 * 1024

def Limits.bodyLimits (limits : Limits) : Multi.Snappy.Limits :=
  { maxStoredPageBytes := limits.maxStoredPageBytes }

inductive FrameError where
  | snappy (cause : Multi.Snappy.FrameError)
  | slots (footer : Int) (page : Nat)
  | groupRows (expected actual : Nat)
  deriving DecidableEq, Repr

/-- Verify the entire original stored body before splitting or expanding its
flag-selected suffix. A missing CRC uses the existing verify-if-present rule. -/
def readSections (limits : Limits) (checked : Checked) (frame : Page.Frame) (info : Page.DataV2) :
    Except Multi.Snappy.FrameError Multi.Snappy.V2Sections := do
  let source := checked.snapshot.bytes
  let _ ← (Page.Checksum.verify limits.maxStoredPageBytes source frame).mapError .checksum
  Multi.Snappy.prepareV2 limits.bodyLimits checked frame info (Page.Checksum.payloadBytes source frame)

structure StoredWire (limits : Limits) (checked : Checked) (frame : Page.Frame)
    (info : Page.DataV2) (sections : Multi.Snappy.V2Sections) : Prop where
  data : ∃ status stored spans,
    Page.Checksum.verify limits.maxStoredPageBytes checked.snapshot.bytes frame = .ok status ∧
    checked.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.maxStoredPageBytes ∧
    frame.v2Spans = some spans ∧
    spans.repetition.stop - spans.repetition.start = sections.repetition.length ∧
    spans.definition.stop - spans.definition.start = sections.definition.length ∧
    spans.values.stop - spans.values.start = frame.value.compressedSize - Multi.Snappy.v2LevelBytes info ∧
    Multi.Snappy.V2BodyWire checked frame info stored sections

/-- Prepare the checksum-checked original V2 body, then decode and validate
its required LIST events. The caller admits the header and bounds the slots. -/
def readEvents (limits : Limits) (checked : Checked) (frame : Page.Frame) (info : Page.DataV2) :
    Except Multi.Snappy.FrameError (List Event) := do
  let sections ← readSections limits checked frame info
  let events ← (RequiredContainer.decodeSections checked.limits.page info.numValues
    sections.repetition sections.definition sections.scalars).mapError .page
  Multi.Snappy.checkV2Counts info events
  pure events

structure EventsWire (limits : Limits) (checked : Checked) (frame : Page.Frame)
    (info : Page.DataV2) (events : List Event) : Prop where
  data : ∃ sections,
    StoredWire limits checked frame info sections ∧
    SectionsWire info.numValues sections.repetition sections.definition sections.scalars events ∧
    Multi.startsWithinRow events = false ∧ Multi.Snappy.pageRows events = info.numRows ∧
    Multi.Snappy.pageNulls events = info.numNulls

def readFrame (limits : Limits) (checked : Checked) (framed : FramedGroup) (frame : Page.Frame) :
    Except FrameError (List Row) := do
  let .dataV2 info := frame.value.kind | throw (.snappy (.page .pageKind))
  if framed.chunk.metadata.codec ≠ 1 then
    return ← throw (.snappy (.page (.codec framed.chunk.metadata.codec)))
  if info.encoding ≠ 0 then return ← throw (.snappy (.page .encoding))
  if framed.chunk.metadata.numValues ≠ (info.numValues : Int) then
    return ← throw (.slots framed.chunk.metadata.numValues info.numValues)
  let expectedRows := framed.group.numRows.toNat
  if checked.limits.page.maxRows < expectedRows ∨ checked.limits.page.maxRows < info.numRows then
    return ← throw (.snappy (.page .rowLimit))
  let events ← (readEvents limits checked frame info).mapError .snappy
  let rows ← (ListPage.reconstruct events).mapError (.snappy ∘ .page)
  if rows.length ≠ expectedRows then return ← throw (.groupRows expectedRows rows.length)
  pure rows

structure FrameWire (limits : Limits) (checked : Checked) (framed : FramedGroup) (frame : Page.Frame)
    (rows : List Row) : Prop where
  parents : ∀ row ∈ rows, row.isSome = true
  data : ∃ info sections,
    frame.value.kind = .dataV2 info ∧ framed.chunk.metadata.codec = 1 ∧ info.encoding = 0 ∧
    StoredWire limits checked frame info sections ∧
    SectionsWire info.numValues sections.repetition sections.definition sections.scalars
      (rows.flatMap ListPage.rowEvents) ∧
    Multi.startsWithinRow (rows.flatMap ListPage.rowEvents) = false ∧
    framed.chunk.metadata.numValues = (info.numValues : Int) ∧
    info.numRows ≤ checked.limits.page.maxRows ∧ rows.length = info.numRows ∧
    rows.length = framed.group.numRows.toNat ∧ rows.length ≤ checked.limits.page.maxRows ∧
    Multi.Snappy.pageNulls (rows.flatMap ListPage.rowEvents) = info.numNulls ∧
    sections.scalars.length = 4 * (info.numValues - info.numNulls) ∧
    Plain.decodeInt32 (info.numValues - info.numNulls) sections.scalars =
      .ok ((rows.flatMap ListPage.rowEvents).filterMap (fun event => event.wire.2.2))

inductive GroupError where
  | framing (cause : ListFile.ReadError)
  | frame (ordinal offset : Nat) (cause : FrameError)
  deriving DecidableEq, Repr

def readGroup (limits : Limits) : RequiredContainer.GroupReader GroupError :=
  RequiredContainer.readGroupWith (fun checked => checked.frameGroupFor 1) .framing fun checked framed frame =>
    (readFrame limits checked framed frame).mapError (.frame 0 frame.header.start)

structure GroupWire (limits : Limits) (checked : Checked) (ordinal : Nat) (rows : List Row) : Prop where
  data : ∃ framed frame,
    ListFile.FramedGroupWire checked ordinal framed 1 ∧
    framed.frames = [frame] ∧ FrameWire limits checked framed frame rows

abbrev SourceError := RequiredContainer.SourceError GroupError
abbrev Error := RequiredContainer.Error GroupError
abbrev Result := RequiredContainer.Result GroupError

def convert (limits : Limits) : Bytes → Result :=
  RequiredContainer.convertUsing (readGroup limits) limits.toLimits

abbrev Readback (limits : Limits) :=
  RequiredContainer.ReadbackUsing (readGroup limits) (GroupWire limits) limits.toLimits

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy
