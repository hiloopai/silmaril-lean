module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.Defs

/-! Opt-in dispatch of the two modern GZIP V1 dictionary TIMESTAMP profiles. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1

open Dictionary (FramedChunk DataPage)

abbrev Limits := Dictionary.Gzip.Limits

inductive Profile where
  | dictionary
  | fallback
  deriving DecidableEq, Repr

def isPlainV1 (frame : Parquet.Page.Frame) : Bool :=
  match frame.value.kind with
  | .dataV1 header => header.encoding == 0
  | _ => false

/-- A PLAIN V1 header selects fallback. The selected profile checks every
original header and its phase order before decoding. -/
def profile (frames : List Parquet.Page.Frame) : Profile :=
  if frames.any isPlainV1 then .fallback else .dictionary

structure Plan where
  framed : FramedChunk
  choice : Profile

def planGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error Plan :=
  (Dictionary.frameGroupUsing .gzipDictionaryV1 limits.dictionary leafLimits bound index).map fun framed =>
    ⟨framed, profile framed.data⟩

/-- Use the selected standalone planner and decoder on the retained frames.
All errors are returned directly from that branch. -/
def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error (Slots bound) := do
  let plan ← planGroup limits leafLimits bound index
  let scalarLimits := limits.withFuel leafLimits
  let readEntries := Dictionary.Gzip.readEntries limits leafLimits bound
  match plan.choice with
  | .dictionary =>
    Dictionary.Snappy.readGroupUsing limits.dictionary scalarLimits bound
      (Dictionary.checkFramedUsing plan.framed (Dictionary.Gzip.planData bound) (fun _ => .ok ()) readEntries)
  | .fallback =>
    Fallback.Snappy.readGroupUsing limits.dictionary scalarLimits bound
      (Dictionary.checkFramedUsing plan.framed (Fallback.Gzip.planData bound) Fallback.checkSequence readEntries)

def readBound (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Open one checked modern TIMESTAMP leaf and emit the selected results
in original footer order. -/
def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (outputLimits : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal
    (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1
