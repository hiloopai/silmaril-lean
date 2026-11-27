module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.Defs

/-! Opt-in Snappy LIST chunks with a PLAIN dictionary, a nonempty run of
RLE_DICTIONARY V2 data pages and a nonempty run of PLAIN V2 data pages. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2

open Snappy (Budget)
open ListPage (Event State Row)

def isDictionaryData (frame : Page.Frame) : Bool :=
  match frame.value.kind with
  | .dataV2 info => info.encoding == 8
  | _ => false

def readPlainFrame (limits : DictionaryV1.Limits) (checked : ListFile.Checked) : DictionaryV1.FrameReader :=
  fun budget frame =>
    if isDictionaryData frame then .error .dictionaryReentry
    else (Snappy.readV2Frame limits.snappy checked budget frame).mapError .v2

/-- Split only the original frame list. Neither body validation nor an error
from the PLAIN suffix runs ahead of the dictionary prefix. -/
def readFrames (limits : DictionaryV1.Limits) (checked : ListFile.Checked) (entries : Array Int32)
    (ordinal : Nat) (budget : Budget) (state : State) (frames : List Page.Frame) :
    Except DictionaryV1.GroupError (Budget × State) := do
  let first :: _ := frames | throw .missingData
  let indexedFrames := frames.takeWhile isDictionaryData
  if indexedFrames.isEmpty then
    return ← throw (.frame ordinal first.header.start .fallbackExpectedDictionary)
  let (left, next) ← DictionaryV1.readFramesUsing (DictionaryV2.readFrame limits checked entries)
    ordinal budget state indexedFrames
  let suffix := frames.dropWhile isDictionaryData
  if suffix.isEmpty then return ← throw .missingPlainSuffix
  DictionaryV1.readFramesUsing (readPlainFrame limits checked) (ordinal + indexedFrames.length) left next suffix

structure FramesWire (limits : DictionaryV1.Limits) (checked : ListFile.Checked) (entries : Array Int32)
    (frames : List Page.Frame) (pages : List (List Event)) : Prop where
  data : ∃ indexedFrames suffix indexed plain,
    indexedFrames ≠ [] ∧ suffix ≠ [] ∧ frames = indexedFrames ++ suffix ∧ pages = indexed ++ plain ∧
    List.Forall₂ (DictionaryV2.FrameWire limits checked entries) indexedFrames indexed ∧
    List.Forall₂ (Snappy.V2FrameWire limits.snappy checked) suffix plain

def walk (limits : DictionaryV1.Limits) : DictionaryV1.DataWalk :=
  fun checked _ => readFrames limits checked

abbrev GroupWire (limits : DictionaryV1.Limits) :=
  DictionaryV1.GroupWireWith limits (fun checked _ => FramesWire limits checked)

def readGroup (limits : DictionaryV1.Limits) (checked : ListFile.Checked) (ordinal expanded : Nat) :
    Except DictionaryV1.GroupError (List Row × Nat) :=
  DictionaryV1.readGroupWith limits (walk limits) checked ordinal expanded

def convert (limits : DictionaryV1.Limits) (source : Bytes) : Snappy.ResultWith DictionaryV1.SourceError DictionaryV1.Error :=
  Snappy.convertWith DictionaryV1.errors limits.snappy (readGroup limits) source

abbrev Readback (limits : DictionaryV1.Limits) (source : Bytes) (wire : KBytes) :=
  Snappy.ReadbackWith DictionaryV1.errors limits.snappy (readGroup limits) (GroupWire limits) source wire

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2
