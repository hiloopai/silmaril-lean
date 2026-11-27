module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Defs
public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.Defs

/-! Opt-in required LIST of nullable INT32 over multiple Snappy-column PLAIN
V2 frames. The original checked chunk decides the codec and frame order. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi

open ListPage (Event Row)
open RequiredContainer (Checked)

structure Limits extends toSnappyLimits : Snappy.Limits where
  maxGroupSlots : Nat := 1024 * 1024

abbrev FrameError := ListFile.Multi.Snappy.FrameError
abbrev GroupError := V2.Multi.GroupError FrameError

/-- Check page admission and slot bounds before the shared checksum and body
reader. The caller supplies a frame of the admitted Snappy chunk. -/
def readFrame (limits : Limits) (checked : Checked) (remaining : Nat) (frame : Page.Frame) :
    Except FrameError (List Event) := do
  let .dataV2 info := frame.value.kind | throw (.page .pageKind)
  if info.encoding ≠ 0 then return ← throw (.page .encoding)
  if remaining < info.numValues then return ← throw (.slotBudget remaining info.numValues)
  if checked.limits.page.maxRows < info.numRows then return ← throw (.page .rowLimit)
  Snappy.readEvents limits.toSnappyLimits checked frame info

structure FrameWire (limits : Limits) (checked : Checked) (frame : Page.Frame) (events : List Event) : Prop where
  data : ∃ info,
    frame.value.kind = .dataV2 info ∧ info.encoding = 0 ∧
    info.numRows ≤ checked.limits.page.maxRows ∧ Snappy.EventsWire limits.toSnappyLimits checked frame info events

def readFrames (limits : Limits) (checked : Checked) :=
  ListFile.Multi.readFramesWith V2.Multi.GroupError.frame ListFile.Multi.Snappy.FrameError.page
    (readFrame limits checked)

def readGroup (limits : Limits) : RequiredContainer.GroupReader GroupError :=
  V2.Multi.readGroupWith (fun checked => checked.frameGroupFor 1) limits.maxGroupSlots
    (readFrame limits) ListFile.Multi.Snappy.FrameError.page

abbrev GroupWire (limits : Limits) (checked : Checked) (ordinal : Nat) (rows : List Row) :=
  V2.Multi.GroupWire limits.maxGroupSlots checked ordinal rows 1 (FrameWire limits checked)

abbrev Result := RequiredContainer.Result GroupError

def convert (limits : Limits) : Bytes → Result :=
  RequiredContainer.convertUsing (readGroup limits) limits.toSnappyLimits.toLimits

abbrev Readback (limits : Limits) :=
  RequiredContainer.ReadbackUsing (readGroup limits) (GroupWire limits) limits.toSnappyLimits.toLimits

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi
