module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Defs

/-! The required-container LIST schema with one uncompressed PLAIN V2 page
per group. V2 stores raw level streams with lengths in the original header. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2

open ListPage (Event Row)
open RequiredContainer (Checked Limits SectionsWire)

inductive FrameError where
  | page (cause : ListPage.Error)
  | bodySize
  | bodyLimit
  | levelExtent
  | levelLimit
  | payloadBounds
  | slots (footer : Int) (page : Nat)
  | pageRows (expected actual : Nat)
  | pageNulls (expected actual : Nat)
  | groupRows (expected actual : Nat)
  deriving DecidableEq, Repr

structure Sections where
  repetition : Bytes
  definition : Bytes
  scalars : Bytes

/-- With codec zero, either resolved suffix flag leaves the original value
bytes raw. Cap the absolute body and each level section before slicing. -/
def readSections (limits : ListPage.Limits) (source : Bytes) (frame : Page.Frame)
    (info : Page.DataV2) : Except FrameError Sections := do
  let size := frame.value.compressedSize
  if size ≠ frame.value.uncompressedSize ∨ frame.payload.stop ≠ frame.payload.start + size then
    return ← throw .bodySize
  if limits.maxBodyBytes < size then return ← throw .bodyLimit
  if size < info.repetitionBytes + info.definitionBytes then return ← throw .levelExtent
  if limits.levels.bytes < info.repetitionBytes ∨ limits.levels.bytes < info.definitionBytes then
    return ← throw .levelLimit
  let some body := source.slice? frame.payload.start (some frame.payload.stop) | throw .payloadBounds
  let bytes := body.toList
  let tail := bytes.drop info.repetitionBytes
  pure ⟨Bytes.ofList (bytes.take info.repetitionBytes),
    Bytes.ofList (tail.take info.definitionBytes), Bytes.ofList (tail.drop info.definitionBytes)⟩

structure RawWire (limits : ListPage.Limits) (source : Bytes) (frame : Page.Frame)
    (info : Page.DataV2) (sections : Sections) : Prop where
  sizes : frame.value.compressedSize = frame.value.uncompressedSize
  bodyLimit : frame.value.compressedSize ≤ limits.maxBodyBytes
  levelLimits : info.repetitionBytes ≤ limits.levels.bytes ∧ info.definitionBytes ≤ limits.levels.bytes
  repetitionSize : sections.repetition.length = info.repetitionBytes
  definitionSize : sections.definition.length = info.definitionBytes
  scalarSize : sections.scalars.length = frame.value.compressedSize - (info.repetitionBytes + info.definitionBytes)
  data : ∃ body spans,
    source.slice? frame.payload.start (some frame.payload.stop) = some body ∧
    body.length = frame.value.compressedSize ∧ frame.v2Spans = some spans ∧
    spans.repetition.stop - spans.repetition.start = sections.repetition.length ∧
    spans.definition.stop - spans.definition.start = sections.definition.length ∧
    spans.values.stop - spans.values.start = sections.scalars.length ∧
    body.toList = sections.repetition.toList ++ sections.definition.toList ++ sections.scalars.toList

/-- V2 counts zero-value slots, including the marker of an empty list. -/
def missingSlots (events : List Event) : Nat :=
  events.countP (fun event => event.wire.2.2.isNone)

def readFrame (checked : Checked) (framed : FramedGroup) (frame : Page.Frame) :
    Except FrameError (List Row) := do
  let .dataV2 info := frame.value.kind | throw (.page .pageKind)
  if framed.chunk.metadata.codec ≠ 0 then return ← throw (.page (.codec framed.chunk.metadata.codec))
  if frame.value.crc.isSome then return ← throw (.page .crc)
  if info.encoding ≠ 0 then return ← throw (.page .encoding)
  if framed.chunk.metadata.numValues ≠ (info.numValues : Int) then
    return ← throw (.slots framed.chunk.metadata.numValues info.numValues)
  let expectedRows := framed.group.numRows.toNat
  if checked.limits.page.maxRows < expectedRows ∨ checked.limits.page.maxRows < info.numRows then
    return ← throw (.page .rowLimit)
  let sections ← readSections checked.limits.page checked.snapshot.bytes frame info
  let events ← (RequiredContainer.decodeSections checked.limits.page info.numValues
    sections.repetition sections.definition sections.scalars).mapError .page
  let absent := missingSlots events
  if absent ≠ info.numNulls then return ← throw (.pageNulls info.numNulls absent)
  let rows ← (ListPage.reconstruct events).mapError .page
  if rows.length ≠ info.numRows then return ← throw (.pageRows info.numRows rows.length)
  if rows.length ≠ expectedRows then return ← throw (.groupRows expectedRows rows.length)
  pure rows

structure FrameWire (checked : Checked) (framed : FramedGroup) (frame : Page.Frame) (rows : List Row) : Prop where
  parents : ∀ row ∈ rows, row.isSome = true
  data : ∃ info sections,
    frame.value.kind = .dataV2 info ∧ framed.chunk.metadata.codec = 0 ∧
    frame.value.crc = none ∧ info.encoding = 0 ∧
    RawWire checked.limits.page checked.snapshot.bytes frame info sections ∧
    SectionsWire info.numValues sections.repetition sections.definition sections.scalars
      (rows.flatMap ListPage.rowEvents) ∧
    framed.chunk.metadata.numValues = (info.numValues : Int) ∧
    rows.length = info.numRows ∧ info.numRows ≤ checked.limits.page.maxRows ∧
    rows.length = framed.group.numRows.toNat ∧
    missingSlots (rows.flatMap ListPage.rowEvents) = info.numNulls ∧
    sections.scalars.length = 4 * (info.numValues - info.numNulls) ∧
    Plain.decodeInt32 (info.numValues - info.numNulls) sections.scalars =
      .ok ((rows.flatMap ListPage.rowEvents).filterMap (fun event => event.wire.2.2))

inductive GroupError where
  | framing (cause : ListFile.ReadError)
  | frame (ordinal offset : Nat) (cause : FrameError)
  deriving DecidableEq, Repr

def readGroup : RequiredContainer.GroupReader GroupError :=
  RequiredContainer.readGroupUsing .framing fun checked framed frame =>
    (readFrame checked framed frame).mapError (.frame 0 frame.header.start)

structure GroupWire (checked : Checked) (ordinal : Nat) (rows : List Row) : Prop where
  data : ∃ framed frame,
    ListFile.FramedGroupWire checked ordinal framed ∧
    framed.frames = [frame] ∧ FrameWire checked framed frame rows

abbrev SourceError := RequiredContainer.SourceError GroupError
abbrev Error := RequiredContainer.Error GroupError
abbrev Result := RequiredContainer.Result GroupError

def convert := RequiredContainer.convertUsing readGroup

abbrev Readback := RequiredContainer.ReadbackUsing readGroup GroupWire

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2
