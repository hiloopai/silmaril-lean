module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Defs
public import Silmaril.Formats.Parquet.DictionaryChunk.Defs

/-! Snappy V1 TIMESTAMP chunks with the deprecated PLAIN_DICTIONARY wire tags. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.LegacyV1

/-- Retain the original encoding and normalize the BIT_PACKED tag only for an
absent level section. Optional definition levels still use RLE. -/
def planDataWith (admits : Int → Bool) (bound : Bound) (frame : Parquet.Page.Frame) : Except DictionaryPageError DataPage := do
  if let .dictionary _ := frame.value.kind then throw .misplacedDictionary
  let .dataV1 info := frame.value.kind | throw (.parameters .unsupportedPage)
  let page ← Snappy.planDataWith admits bound frame
  let defTag := DictionaryChunk.Internal.levelTag bound.levels.maxDefinition info.definitionLevelEncoding
  let repTag := DictionaryChunk.Internal.levelTag bound.levels.maxRepetition info.repetitionLevelEncoding
  return {page with params.version := .v1 defTag repTag}

def planData := planDataWith (· == 2)

/-- Require one leading tag-2 dictionary and only tag-2 V1 data pages. -/
def checkGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error CheckedChunk :=
  Dictionary.checkGroupUsing .snappyLegacyDictionaryV1 limits leafLimits bound index
    (planData bound) (fun _ => .ok ()) (Snappy.readEntriesWith .plainDictionary limits leafLimits bound)

def readGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error (Slots bound) :=
  Snappy.readGroupUsing limits leafLimits bound (checkGroup limits leafLimits bound index)

def readBound (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Opt in to the deprecated encodings for a modern flat INT64 TIMESTAMP. -/
def convert (limits : Dictionary.Limits) (inputLimits : Events.ToIpc.Limits)
    (outputLimits : Arrow.ObservationLimits) (input : Bytes) (ordinal : Nat) :
    Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal
    (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.LegacyV1
