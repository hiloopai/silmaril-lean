module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.Defs

/-! Select a checked TIMESTAMP chunk profile independently in each footer group. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups

open Dictionary (CheckedChunk DataPage)

/-- Codec admission is explicit at this entry point. -/
inductive DictionaryCodec where
  | uncompressed
  | snappy
  deriving DecidableEq, Repr

def DictionaryCodec.encoding : DictionaryCodec → ChunkEncoding
  | .uncompressed => .dictionary
  | .snappy => .snappyDictionary

def DictionaryCodec.id : DictionaryCodec → Int
  | .uncompressed => 0
  | .snappy => 1

/-- None selects PLAIN. A dictionary offset selects the corresponding
dictionary planner. The normal selector still checks metadata and spans. -/
def route (metadata : Footer.ColumnMetadata) : Except Leaf.Error (Option DictionaryCodec) :=
  if metadata.codec = 0 then
    .ok (if metadata.dictionaryPageOffset.isSome then some .uncompressed else none)
  else if metadata.codec = 1 then
    .ok (if metadata.dictionaryPageOffset.isSome then some .snappy else none)
  else .error (.chunkCodec metadata.codec)

inductive DictionaryLayout where
  | references
  | fallback
  deriving DecidableEq, Repr

/-- Wire tags that witness the selected dictionary data layout. -/
def DictionaryLayout.Wire (layout : DictionaryLayout) (pages : List DataPage) : Prop :=
  match layout with
  | .references => pages ≠ [] ∧ ∀ page ∈ pages, page.params.encoding = 8
  | .fallback => Fallback.Ordered pages

def dictionaryLayout (pages : List DataPage) : DictionaryLayout :=
  if pages.all Fallback.isDictionary then .references else .fallback

def checkSequence (pages : List DataPage) : Except Leaf.Error Unit :=
  match dictionaryLayout pages with
  | .references => if pages.isEmpty then .error .dictionaryMissingData else .ok ()
  | .fallback => Fallback.checkSequence pages

inductive Plan where
  | plain (chunk : Leaf.Chunk) (pages : List DataPage)
  | dictionary (codec : DictionaryCodec) (layout : DictionaryLayout) (chunk : CheckedChunk)

def planPlainPage (bound : Bound) (codec : Int) (frame : Parquet.Page.Frame) (ordinal : Nat) :
    Except Leaf.Error DataPage := do
  let params ← (Timestamp.Page.parameters bound.binding.leaf bound.levels codec frame.value).mapError (.page ordinal)
  if params.encoding ≠ 0 then Except.error (.page ordinal (.scalar (.unsupportedEncoding params.encoding)))
  return ⟨frame, params⟩

def planPlain (limits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error Plan := do
  let chunk ← Leaf.selectChunk {limits with allowSnappy := true} bound index
  let frames ← (Parquet.Page.readChunk limits.framing bound.snapshot.bytes chunk.span).mapError .framing
  let expected := chunk.group.numRows.toNat
  let actual := (frames.map Leaf.Internal.pageSlots).sum
  if actual ≠ expected then Except.error (.rowCount expected actual)
  let pages ← frames.zipIdx.mapM fun (frame, ordinal) =>
    planPlainPage bound chunk.column.metadata.codec frame ordinal
  return .plain chunk pages

def planData (codec : DictionaryCodec) (bound : Bound) :
    Parquet.Page.Frame → Except DictionaryPageError DataPage :=
  match codec with
  | .uncompressed => Dictionary.planDataWith Fallback.admits bound
  | .snappy => Dictionary.Snappy.planDataWith Fallback.admits bound

def readEntries (codec : DictionaryCodec) (limits : Dictionary.Limits) (leafLimits : Leaf.Limits)
    (bound : Bound) : Parquet.Page.Frame → Except DictionaryPageError (List Int64) :=
  match codec with
  | .uncompressed => Dictionary.readEntries limits bound
  | .snappy => Dictionary.Snappy.readEntries limits leafLimits bound

def planDictionary (codec : DictionaryCodec) (limits : Dictionary.Limits) (leafLimits : Leaf.Limits)
    (bound : Bound) (index : Nat) : Except Leaf.Error Plan := do
  let chunk ← Dictionary.checkGroupUsing codec.encoding limits leafLimits bound index
    (planData codec bound) checkSequence (readEntries codec limits leafLimits bound)
  return .dictionary codec (dictionaryLayout chunk.data) chunk

/-- Choose once from the exact selected footer entry. The strict snapshot
requires positive chunk spans, so page-less groups fail at open. -/
def planGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error Plan := do
  let some group := bound.snapshot.groupAt index | Except.error (.groupIndex index)
  let columnIndex := bound.ordinal - 1
  let some column := group.columns[columnIndex]? | Except.error (.chunkIndex columnIndex)
  match ← route column.metadata with
  | none => planPlain leafLimits bound index
  | some codec => planDictionary codec limits leafLimits bound index

def decodeDictionaryPage (codec : DictionaryCodec) (layout : DictionaryLayout)
    (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (entries : Array Int64) :
    DataPage → Nat → Except Leaf.Error (List (Option Int64)) :=
  match codec, layout with
  | .uncompressed, .references => Dictionary.decodePage limits leafLimits bound entries
  | .uncompressed, .fallback => Fallback.decodePage limits leafLimits bound entries
  | .snappy, .references => Dictionary.Snappy.decodePage limits leafLimits bound entries
  | .snappy, .fallback => Fallback.Snappy.decodePage limits leafLimits bound entries

def decodePlan (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Plan → Except Leaf.Error (Slots bound)
  | .plain chunk pages => do
    let values ← pages.zipIdx.mapM fun (page, ordinal) =>
      Leaf.Internal.decodeFrame leafLimits.page bound chunk.column.metadata.codec page.frame ordinal
    return values.flatten
  | .dictionary codec layout chunk => do
    let entries := chunk.entries.toArray
    let values ← (chunk.data.zipIdx 1).mapM fun (page, ordinal) =>
      decodeDictionaryPage codec layout limits leafLimits bound entries page ordinal
    return values.flatten.map (Option.map bound.binding.descriptor.decode)

def readGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) : Except Leaf.Error (Slots bound) := do
  let plan ← planGroup limits leafLimits bound index
  decodePlan limits leafLimits bound plan

def readBound (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

def convert (profile : AnnotationProfile) (limits : Dictionary.Limits) (inputLimits : Events.ToIpc.Limits)
    (outputLimits : Arrow.ObservationLimits) (input : Bytes) (ordinal : Nat) :
    Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups profile inputLimits outputLimits input ordinal (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups
