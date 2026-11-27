module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.V2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2.Defs

/-! Opt-in dispatch between strict modern GZIP V2 TIMESTAMP chunk profiles. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2

abbrev Limits := Dictionary.Gzip.Limits

/-- The original dictionary offset determines which framing path to use.
The chosen path still checks the column association, footer layout and bounds. -/
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
    Except Leaf.Error DictionaryPlan :=
  (Dictionary.frameGroupUsing .gzipDictionaryV2 limits.dictionary leafLimits bound index).map fun framed =>
    ⟨framed, dictionaryProfile framed.data⟩

/-- Classify the original dictionary-backed frames once and use the chosen
strict planner and decoder on those frames. -/
def readDictionary (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error (Slots bound) := do
  let plan ← planDictionary limits leafLimits bound index
  let scalarLimits := limits.withFuel leafLimits
  let readEntries := Dictionary.Gzip.readEntries limits leafLimits bound
  match plan.profile with
  | .references =>
    Dictionary.Snappy.readGroupUsing limits.dictionary scalarLimits bound
      (Dictionary.checkFramedUsing plan.framed (Dictionary.Gzip.V2.planData bound) (fun _ => .ok ()) readEntries)
  | .fallback =>
    Fallback.Snappy.readGroupUsing limits.dictionary scalarLimits bound
      (Dictionary.checkFramedUsing plan.framed (Fallback.Gzip.V2.planData bound) Fallback.checkSequence readEntries)

def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error (Slots bound) := do
  if ← hasDictionary bound index then
    readDictionary limits leafLimits bound index
  else
    Gzip.V2.readGroup limits leafLimits bound index

def readBound (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) : Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Open a checked modern leaf and emit one native IPC batch per footer group. -/
def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (outputLimits : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal
    (readGroup limits inputLimits.leaf)

-- The chosen decoder's exact original pages and their reconstructed, ordered slots.
def DictionaryWire (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) (plan : DictionaryPlan) (slots : Slots bound) : Prop :=
  ∃ checked pages,
    (match plan.profile with
     | .references => Dictionary.Gzip.V2.checkGroup limits leafLimits bound index
     | .fallback => Fallback.Gzip.V2.checkGroup limits leafLimits bound index) = .ok checked ∧
    checked.frames = plan.framed.frames ∧
    Dictionary.Gzip.readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
    List.Forall₂ (fun page raw =>
      match plan.profile with
      | .references => Dictionary.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
          bound checked.entries.toArray page raw
      | .fallback => Fallback.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
          bound checked.entries.toArray page raw) checked.data pages ∧
    slots.map (Option.map Silmaril.Numeric.Timestamp.Ticks.ticks) =
      pages.flatten.map (Option.map Int64.toInt) ∧
    slots.length = checked.chunk.group.numRows.toNat

/-- The original group has one selected set of page witnesses. -/
inductive GroupWire (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) (slots : Slots bound) : Prop where
  | plain {group : Gzip.V2.CheckedGroup} {pages : List (List (Option Int64))}
      (route : hasDictionary bound index = .ok false)
      (checked : Gzip.V2.checkGroup limits leafLimits bound index = .ok group)
      (decoded : List.Forall₂ (Gzip.V2.PageWire (limits.withFuel leafLimits).page bound) group.frames pages)
      (ordered : slots = pages.flatten.map (Option.map bound.binding.descriptor.decode))
      (rows : slots.length = group.chunk.group.numRows.toNat)
  | dictionary {plan : DictionaryPlan}
      (route : hasDictionary bound index = .ok true)
      (planned : planDictionary limits leafLimits bound index = .ok plan)
      (decoded : DictionaryWire limits leafLimits bound index plan slots)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2
