module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.Defs

/-! Opt-in dispatch among the three strict modern Zstandard V2 TIMESTAMP profiles. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2

open Silmaril.Numeric.Timestamp (Ticks)

abbrev Limits := Dictionary.Zstd.V2.Limits
abbrev GroupError := Leaf.Zstd.V2.GroupError
abbrev Error := Leaf.Zstd.V2.Error

/-- Use only the selected footer column's original dictionary offset to
choose the framing path. The chosen reader still checks the full selection. -/
def hasDictionary (bound : Bound) (index : Nat) : Except Leaf.Error Bool := do
  let some group := bound.snapshot.groupAt index | throw (.groupIndex index)
  let columnIndex := bound.ordinal - 1
  let some column := group.columns[columnIndex]? | throw (.chunkIndex columnIndex)
  return column.metadata.dictionaryPageOffset.isSome

inductive DictionaryProfile where
  | references
  | fallback
  deriving DecidableEq, Repr

def isPlainV2 (frame : Parquet.Page.Frame) : Bool :=
  match frame.value.kind with
  | .dataV2 header => header.encoding == 0
  | _ => false

def dictionaryProfile (frames : List Parquet.Page.Frame) : DictionaryProfile :=
  if frames.any isPlainV2 then .fallback else .references

structure DictionaryPlan where
  framed : Dictionary.FramedChunk
  profile : DictionaryProfile

def planDictionary (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError DictionaryPlan :=
  ((Dictionary.frameGroupUsing .zstdDictionaryV2 limits.dictionary leafLimits bound index).mapError
    .selection).map fun framed => ⟨framed, dictionaryProfile framed.data⟩

/-- Classify the original dictionary-backed frames once, then run only the
selected planner and decoder on those frames. -/
def readDictionary (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError (Slots bound) := do
  let plan ← planDictionary limits leafLimits bound index
  match plan.profile with
  | .references =>
    Dictionary.Zstd.V2.readGroupUsing bound (Dictionary.Zstd.V2.decodePage limits leafLimits bound)
      (Dictionary.Zstd.V2.checkFramedWith (· == 8) (fun _ => .ok ()) limits leafLimits bound plan.framed)
  | .fallback =>
    Dictionary.Zstd.V2.readGroupUsing bound (Fallback.Zstd.V2.decodePage limits leafLimits bound)
      (Dictionary.Zstd.V2.checkFramedWith Fallback.admits Fallback.checkSequence limits leafLimits bound plan.framed)

def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError (Slots bound) := do
  if ← (hasDictionary bound index).mapError .selection then
    readDictionary limits leafLimits bound index
  else
    Leaf.Zstd.V2.readGroup (Dictionary.Zstd.V2.scalarLimits limits) leafLimits bound index

def readBound (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) : Leaf.Zstd.V2.Source :=
  Leaf.Zstd.V2.readBoundWith bound (readGroup limits leafLimits bound)

/-- Select the modern leaf once and emit one native Arrow batch per original footer group. -/
def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (output : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Error KBytes :=
  Leaf.Zstd.V2.convertWith inputLimits output input ordinal (readGroup limits inputLimits.leaf)

/-- Original frames and bounded payload evidence from the selected dictionary branch. -/
def DictionaryWire (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) (plan : DictionaryPlan) (slots : Slots bound) : Prop :=
  ∃ checked pages,
    (match plan.profile with
     | .references => Dictionary.Zstd.V2.checkGroup limits leafLimits bound index
     | .fallback => Fallback.Zstd.V2.checkGroup limits leafLimits bound index) = .ok checked ∧
    checked.frames = plan.framed.frames ∧
    (checked.frames.map (·.value.uncompressedSize)).sum ≤ limits.maxExpandedChunkBytes ∧
    Dictionary.Zstd.V2.DictionaryWire limits leafLimits bound checked.dictionary checked.entries ∧
    List.Forall₂ (fun page raw =>
      match plan.profile with
      | .references => Dictionary.Zstd.V2.PageWire limits leafLimits bound checked.entries.toArray page raw
      | .fallback => Fallback.Zstd.V2.PageWire limits leafLimits bound checked.entries.toArray page raw)
      checked.data pages ∧
    slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
    slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
    slots.length = checked.chunk.group.numRows.toNat

/-- Every completed group keeps its selected strict reader's original wire witnesses. -/
inductive GroupWire (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) (slots : Slots bound) : Prop where
  | plain {group : Leaf.Zstd.V2.CheckedGroup} {pages : List (List (Option Int64))}
      (route : hasDictionary bound index = .ok false)
      (checked : Leaf.Zstd.V2.checkGroup (Dictionary.Zstd.V2.scalarLimits limits) leafLimits bound index = .ok group)
      (decoded : List.Forall₂ (Leaf.Zstd.V2.PageWire (Dictionary.Zstd.V2.scalarLimits limits) leafLimits bound)
        group.frames pages)
      (ordered : slots = pages.flatten.map (Option.map bound.binding.descriptor.decode))
      (ticks : slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt))
      (rows : slots.length = group.chunk.group.numRows.toNat)
  | dictionary {plan : DictionaryPlan}
      (route : hasDictionary bound index = .ok true)
      (planned : planDictionary limits leafLimits bound index = .ok plan)
      (decoded : DictionaryWire limits leafLimits bound index plan slots)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2
