module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Defs

/-! Snappy TIMESTAMP chunks with one dictionary and an explicit PLAIN suffix. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy

open Dictionary (CheckedChunk DataPage)

/-- Use codec 1 with the checked dictionary prefix and PLAIN suffix policy. -/
def checkGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error CheckedChunk :=
  Dictionary.checkGroupUsing .snappyDictionary limits leafLimits bound index
    (Dictionary.Snappy.planDataWith Fallback.admits bound) Fallback.checkSequence
    (Dictionary.Snappy.readEntries limits leafLimits bound)

/-- Verify the original stored data frame before dispatching the original
header to either decoder. -/
def decodePage (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (entries : Array Int64) (page : DataPage) (ordinal : Nat) : Except Leaf.Error (List (Option Int64)) := do
  let _ ← Dictionary.Snappy.verifyData leafLimits bound page ordinal
  Fallback.decodePage limits leafLimits bound entries page ordinal

/-- The stored payload is verified and the original header selects a single
physical decoder. -/
def DataWire (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (entries : Array Int64) (page : DataPage) (slots : List (Option Int64)) : Prop :=
  ∃ status,
    Parquet.Page.Checksum.verify leafLimits.page.compressedBytes bound.snapshot.bytes page.frame = .ok status ∧
    Fallback.PageWire limits leafLimits bound entries page slots

def readGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error (Slots bound) := do
  let checked ← checkGroup limits leafLimits bound index
  let entries := checked.entries.toArray
  let pages ← (checked.data.zipIdx 1).mapM fun (page, ordinal) =>
    decodePage limits leafLimits bound entries page ordinal
  return pages.flatten.map (Option.map bound.binding.descriptor.decode)

def readBound (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Explicitly select the Snappy dictionary-to-PLAIN profile for this leaf. -/
def convert (profile : AnnotationProfile) (limits : Dictionary.Limits) (inputLimits : Events.ToIpc.Limits)
    (outputLimits : Arrow.ObservationLimits) (input : Bytes) (ordinal : Nat) :
    Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups profile inputLimits outputLimits input ordinal (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy
