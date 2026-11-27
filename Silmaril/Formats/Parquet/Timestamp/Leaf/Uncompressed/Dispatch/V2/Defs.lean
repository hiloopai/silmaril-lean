module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2.Defs

/-! Opt-in dispatch between strict codec-0 V2 TIMESTAMP chunk profiles. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.Dispatch.V2

/-- Use the original footer column's dictionary offset, independently of its codec. -/
abbrev hasDictionary := Leaf.Snappy.Dispatch.V2.hasDictionary

abbrev isPlainV2 := Leaf.Snappy.Dispatch.V2.isPlainV2

structure HeaderPlan where
  hasPlain : Bool
  data : Except Leaf.Error (List Dictionary.DataPage)

def planAt (bound : Bound) (frame : Parquet.Page.Frame) (ordinal : Nat) :
    Except Leaf.Error Dictionary.DataPage :=
  (Fallback.Uncompressed.V2.planData bound frame).mapError (Dictionary.atFrame ordinal frame)

/-- Walk the framed data once. Retain the first planning failure while still
checking later headers for the profile's PLAIN tag. No bodies are read here. -/
def scanHeaders (bound : Bound) : List Parquet.Page.Frame → Nat → Bool →
    Except Leaf.Error (List Dictionary.DataPage) → HeaderPlan
  | [], _, hasPlain, reversed => ⟨hasPlain, reversed.map List.reverse⟩
  | frame :: rest, ordinal, hasPlain, reversed =>
    let planned := do
      let earlier ← reversed
      let page ← planAt bound frame ordinal
      return page :: earlier
    scanHeaders bound rest (ordinal + 1) (hasPlain || isPlainV2 frame) planned

structure DictionaryPlan where
  framed : Dictionary.FramedChunk
  headers : HeaderPlan

def planDictionary (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error DictionaryPlan :=
  (Dictionary.frameGroupUsing .dictionary limits leafLimits bound index).map fun framed =>
    ⟨framed, scanHeaders bound framed.data 1 false (.ok [])⟩

/-- Complete the selected strict profile using the planned headers, without
reframing or planning any original data header a second time. -/
def readDictionary (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error (Slots bound) := do
  let plan ← planDictionary limits leafLimits bound index
  let data ← plan.headers.data
  let readEntries := Dictionary.Uncompressed.V2.readEntries limits leafLimits bound
  if plan.headers.hasPlain then
    Fallback.Snappy.readGroupUsing limits leafLimits bound
      (Dictionary.checkPlannedUsing plan.framed data Fallback.checkSequence readEntries)
  else
    Dictionary.Snappy.readGroupUsing limits leafLimits bound
      (Dictionary.checkPlannedUsing plan.framed data (fun _ => .ok ()) readEntries)

def readGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error (Slots bound) := do
  if ← hasDictionary bound index then
    readDictionary limits leafLimits bound index
  else
    Leaf.Uncompressed.V2.readGroup leafLimits bound index

def readBound (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) : Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Select the strict modern codec-0 profile per original row group and emit
one native Arrow batch per complete group. -/
def convert (limits : Dictionary.Limits) (inputLimits : Events.ToIpc.Limits) (outputLimits : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal
    (readGroup limits inputLimits.leaf)

/-- The selected decoder's original pages and their reconstructed, ordered slots. -/
def DictionaryWire (limits : Leaf.Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) (plan : DictionaryPlan) (slots : Slots bound) : Prop :=
  ∃ checked pages,
    (if plan.headers.hasPlain then Fallback.Uncompressed.V2.checkGroup limits leafLimits bound index
     else Dictionary.Uncompressed.V2.checkGroup limits leafLimits bound index) = .ok checked ∧
    checked.frames = plan.framed.frames ∧
    Dictionary.Uncompressed.V2.readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
    List.Forall₂ (fun page raw =>
      if plan.headers.hasPlain then Fallback.Snappy.DataWire limits leafLimits bound checked.entries.toArray page raw
      else Dictionary.Snappy.DataWire limits leafLimits bound checked.entries.toArray page raw) checked.data pages ∧
    slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
    slots.map (Option.map Silmaril.Numeric.Timestamp.Ticks.ticks) =
      pages.flatten.map (Option.map Int64.toInt) ∧
    slots.length = checked.chunk.group.numRows.toNat

/-- The original group has one selected set of page witnesses. -/
inductive GroupWire (limits : Leaf.Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) (slots : Slots bound) : Prop where
  | plain {group : Leaf.Uncompressed.V2.CheckedGroup} {pages : List (List (Option Int64))}
      (route : hasDictionary bound index = .ok false)
      (checked : Leaf.Uncompressed.V2.checkGroup leafLimits bound index = .ok group)
      (decoded : List.Forall₂ (Leaf.Uncompressed.V2.PageWire leafLimits.page bound) group.frames pages)
      (ordered : slots = pages.flatten.map (Option.map bound.binding.descriptor.decode))
      (ticks : slots.map (Option.map Silmaril.Numeric.Timestamp.Ticks.ticks) =
        pages.flatten.map (Option.map Int64.toInt))
      (rows : slots.length = group.chunk.group.numRows.toNat)
  | dictionary {plan : DictionaryPlan}
      (route : hasDictionary bound index = .ok true)
      (planned : planDictionary limits leafLimits bound index = .ok plan)
      (decoded : DictionaryWire limits leafLimits bound index plan slots)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.Dispatch.V2
