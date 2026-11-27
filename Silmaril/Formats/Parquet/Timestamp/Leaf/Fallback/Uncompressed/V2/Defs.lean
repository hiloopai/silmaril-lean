module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Defs

/-! Opt-in codec-0 V2 TIMESTAMP with one dictionary followed by a PLAIN suffix. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2

open Dictionary (CheckedChunk DataPage)

def planData (bound : Bound) (frame : Parquet.Page.Frame) : Except DictionaryPageError DataPage :=
  Dictionary.Uncompressed.V2.planDataWith Fallback.admits bound frame

/-- Check the original dictionary, page sequence and declared row count before
decoding any original data body. -/
def checkGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error CheckedChunk :=
  Dictionary.checkGroupUsing .dictionary limits leafLimits bound index
    (planData bound) Fallback.checkSequence (Dictionary.Uncompressed.V2.readEntries limits leafLimits bound)

def readGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error (Slots bound) :=
  Fallback.Snappy.readGroupUsing limits leafLimits bound (checkGroup limits leafLimits bound index)

def readBound (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Convert the selected modern TIMESTAMP leaf with an explicit V2 fallback. -/
def convert (limits : Dictionary.Limits) (inputLimits : Events.ToIpc.Limits) (outputLimits : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal
    (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2
