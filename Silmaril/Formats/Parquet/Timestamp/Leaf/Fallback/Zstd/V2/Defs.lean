module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Zstd.V2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Defs

/-! Opt-in modern Zstandard TIMESTAMP dictionary-to-PLAIN Data Page V2. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2

open Dictionary (DataPage CheckedChunk)

abbrev Limits := Dictionary.Zstd.V2.Limits
abbrev GroupError := Leaf.Zstd.V2.GroupError
abbrev Error := Leaf.Zstd.V2.Error

def planData (bound : Bound) (frame : Parquet.Page.Frame) : Except DictionaryPageError DataPage :=
  Dictionary.Zstd.V2.planDataWith Fallback.admits bound frame

/-- Admit one leading dictionary and a nonempty reference phase followed by a
nonempty PLAIN suffix on the original data frames. -/
def checkGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError CheckedChunk :=
  Dictionary.Zstd.V2.checkGroupWith Fallback.admits Fallback.checkSequence limits leafLimits bound index

/-- The admitted tag selects its strict decoder on the original frame and offset. -/
def decodePage (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (entries : Array Int64)
    (page : DataPage) (ordinal : Nat) : Except GroupError (List (Option Int64)) :=
  if page.params.encoding = 0 then
    Leaf.Zstd.V2.decodePage (Dictionary.Zstd.V2.scalarLimits limits) leafLimits bound page.frame ordinal
  else
    Dictionary.Zstd.V2.decodePage limits leafLimits bound entries page ordinal

def PageWire (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (entries : Array Int64)
    (page : DataPage) (slots : List (Option Int64)) : Prop :=
  slots.length = page.params.numValues ∧
    ((page.params.encoding = 8 ∧ Dictionary.Zstd.V2.PageWire limits leafLimits bound entries page slots) ∨
     (page.params.encoding = 0 ∧ Leaf.Zstd.V2.PageWire (Dictionary.Zstd.V2.scalarLimits limits)
       leafLimits bound page.frame slots))

def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError (Slots bound) := do
  let checked ← checkGroup limits leafLimits bound index
  let entries := checked.entries.toArray
  let pages ← (checked.data.zipIdx 1).mapM fun (page, ordinal) =>
    decodePage limits leafLimits bound entries page ordinal
  return pages.flatten.map (Option.map bound.binding.descriptor.decode)

def readBound (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) : Leaf.Zstd.V2.Source :=
  Leaf.Zstd.V2.readBoundWith bound (readGroup limits leafLimits bound)

/-- Read the selected modern TIMESTAMP leaf and emit native IPC after source EOS. -/
def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (output : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Error KBytes :=
  Leaf.Zstd.V2.convertWith inputLimits output input ordinal (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2
