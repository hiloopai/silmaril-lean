module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Defs
public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2.Defs

/-! Opt-in selected GZIP DATE with an original PLAIN dictionary and
nonempty RLE_DICTIONARY then PLAIN phases of Data Page V2. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2

open DictionaryChunk (DataPage)

abbrev Limits := Gzip.Limits
abbrev CheckedGroup := Gzip.CheckedGroup

inductive HeaderError where
  | expectedV2
  | encoding (actual : Int)
  deriving DecidableEq, Repr

inductive GroupError where
  | chunk (cause : Dictionary.Snappy.GroupError)
  | header (page offset : Nat) (cause : HeaderError)
  | sequence (cause : Fallback.GroupError)
  | plain (page offset : Nat) (cause : ScalarPage.Error)
  deriving DecidableEq, Repr

inductive Error where
  | openFailure (cause : Leaf.Error)
  | groupFailure (index : Nat) (cause : GroupError)
  deriving DecidableEq, Repr

inductive IpcError where
  | source (cause : Error)
  | closed
  | writer (cause : Arrow.DateStream.Writer.Error)
  deriving DecidableEq, Repr

def planData (bound : Bound) (frame : Page.Frame) : Except HeaderError DataPage := do
  let .dataV2 header := frame.value.kind | throw .expectedV2
  if header.encoding ≠ 8 ∧ header.encoding ≠ 0 then throw (.encoding header.encoding)
  let some params := FlatScan.int32PageParameters bound.field frame.value | throw .expectedV2
  return ⟨frame, { params with codec := Payload.Codec.gzip.id }⟩

def planPages (bound : Bound) (frames : List Page.Frame) : Except GroupError (List DataPage) :=
  Fallback.planPagesWith (planData bound) (fun ordinal frame => GroupError.header ordinal frame.header.start)
    id .sequence frames

/-- Dictionary pages keep their whole-body GZIP representation in a V2 chunk. -/
def checkGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError CheckedGroup :=
  Dictionary.Snappy.checkGroupWithCodec .gzip .chunk (Gzip.readEntries limits) (planPages bound)
    limits.toDictionaryLimits bound index

def decodePage (limits : Limits) (source : Bytes) (entries : Array Int32)
    (page : DataPage) (ordinal : Nat) : Except GroupError Slots :=
  Gzip.decodePageWith .chunk .plain limits source entries page ordinal

def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots :=
  Gzip.readGroupWith (checkGroup limits bound) (decodePage limits) bound index

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Emit complete Date32 IPC only after the checked source reaches EOF. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

/-- Original checksummed V2 levels and suffix, and the exact typed observation
of the scalar encoding selected in the original header. -/
structure PageWire (limits : Limits) (source : Bytes) (entries : Array Int32) (page : DataPage)
    (slots : Slots) : Prop where
  count : slots.length = page.params.numValues
  wire : ∃ header, ∃ prepared : ScalarPage.Prepared,
    Date.Leaf.Gzip.V2.PreparedFrame limits.scalar source page.frame header page.params.schema prepared ∧
    header.encoding = page.params.encoding ∧ header.numValues = page.params.numValues ∧
    slots.map Option.isSome = prepared.mask ∧
    (slots.filterMap id).length + header.numNulls = header.numValues ∧
    ((header.encoding = 8 ∧ ∃ width runs indices,
      prepared.scalars.toList = width :: runs ∧ width.toNat ≤ 32 ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      indices.map (fun index => entries[index]?) = (slots.filterMap id).map some) ∨
      (header.encoding = 0 ∧ ScalarPage.Kind.int32.readPlain (prepared.mask.count true)
        prepared.scalars = .ok (slots.filterMap id)))

end Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.V2
