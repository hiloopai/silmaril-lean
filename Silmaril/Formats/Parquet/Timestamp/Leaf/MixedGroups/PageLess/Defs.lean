module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.Defs

/-! Explicitly retain PyArrow-style page-less groups alongside framed TIMESTAMP groups. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess

def openLeaf (profile : AnnotationProfile) (limits : Snapshot.Limits) (input : Bytes)
    (ordinal : Nat) : Except Leaf.Error Bound := do
  let checked ← (Snapshot.checkPageLessTimestamp limits input).mapError .pageLessSnapshot
  bindWith profile limits.footer checked ordinal

def openBound (profile : AnnotationProfile) (limits : Events.ToIpc.Limits) (input : Bytes)
    (ordinal : Nat) : Except Events.ToIpc.Error Bound :=
  Events.ToIpc.openBoundUsing limits input (fun bytes => openLeaf profile limits.snapshot bytes ordinal)

/-- Return an explicit empty batch only for an original group admitted by
the no-frame snapshot profile. Framed groups use the original mixed plan. -/
def readGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error (Slots bound) :=
  match bound.snapshot.groupAt index with
  | none => .error (.groupIndex index)
  | some group =>
    if bound.snapshot.admitsPageLessTimestamp group then .ok []
    else MixedGroups.readGroup limits leafLimits bound index

def readBound (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

def convert (profile : AnnotationProfile) (limits : Dictionary.Limits) (inputLimits : Events.ToIpc.Limits)
    (outputLimits : Arrow.ObservationLimits) (input : Bytes) (ordinal : Nat) :
    Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroupsUsing (openBound profile inputLimits input ordinal)
    outputLimits (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess
