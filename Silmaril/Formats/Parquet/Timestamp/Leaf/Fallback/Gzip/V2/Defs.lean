module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Defs

/-! Opt-in GZIP V2 TIMESTAMP with one dictionary followed by a PLAIN suffix. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2

open Dictionary (CheckedChunk DataPage)

abbrev Limits := Dictionary.Gzip.Limits

def planData (bound : Bound) (frame : Parquet.Page.Frame) : Except DictionaryPageError DataPage :=
  Dictionary.Gzip.V2.planDataWith Fallback.admits bound frame

/-- Check the original dictionary, page sequence and declared row count before
decoding any original GZIP body. -/
def checkGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error CheckedChunk :=
  Dictionary.checkGroupUsing .gzipDictionaryV2 limits.dictionary leafLimits bound index
    (planData bound) Fallback.checkSequence (Dictionary.Gzip.readEntries limits leafLimits bound)

def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error (Slots bound) :=
  Snappy.readGroupUsing limits.dictionary (limits.withFuel leafLimits) bound (checkGroup limits leafLimits bound index)

def readBound (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Convert the selected modern TIMESTAMP leaf with an explicit V2 fallback. -/
def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (outputLimits : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal
    (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2
