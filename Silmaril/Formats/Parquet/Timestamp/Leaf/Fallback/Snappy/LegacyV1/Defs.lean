module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.LegacyV1.Defs

/-! Original Snappy V1 TIMESTAMP pages with a tag-2 dictionary and PLAIN fallback. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.LegacyV1

open Dictionary (CheckedChunk DataPage)

def planData (bound : Bound) (frame : Parquet.Page.Frame) : Except DictionaryPageError DataPage :=
  Dictionary.Snappy.LegacyV1.planDataWith (fun tag => tag == 2 || tag == 0) bound frame

/-- Require one tag-2 dictionary and a nonempty tag-2 prefix followed by a
nonempty PLAIN suffix. Page sequence and row count precede body decoding. -/
def checkGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error CheckedChunk :=
  Dictionary.checkGroupUsing .snappyLegacyFallbackV1 limits leafLimits bound index
    (planData bound) (Fallback.checkSequenceWith 2)
    (Dictionary.Snappy.readEntriesWith .plainDictionary limits leafLimits bound)

def readGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error (Slots bound) :=
  Snappy.readGroupUsing limits leafLimits bound (checkGroup limits leafLimits bound index)

def readBound (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Select the legacy V1 fallback encoding for a modern flat INT64 TIMESTAMP. -/
def convert (limits : Dictionary.Limits) (inputLimits : Events.ToIpc.Limits)
    (outputLimits : Arrow.ObservationLimits) (input : Bytes) (ordinal : Nat) :
    Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal
    (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.LegacyV1
