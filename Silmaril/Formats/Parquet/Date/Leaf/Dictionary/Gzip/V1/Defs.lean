module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Defs

/-! Opt-in selected GZIP DATE with a PLAIN dictionary and only
RLE_DICTIONARY V1 data pages. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1

open DictionaryChunk (DataPage)

abbrev Limits := Fallback.Gzip.Limits
abbrev CheckedGroup := Fallback.Gzip.CheckedGroup
abbrev HeaderError := Fallback.Gzip.HeaderError

inductive GroupError where
  | chunk (cause : Dictionary.Snappy.GroupError)
  | header (page offset : Nat) (cause : HeaderError)
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

/-- The existing V1 plan retains the header and level encodings.
Admit only the modern dictionary reference tag. -/
def planData (bound : Bound) (frame : Page.Frame) : Except HeaderError DataPage := do
  let page ← Fallback.Gzip.planData bound frame
  if page.params.encoding ≠ 8 then throw (.encoding page.params.encoding)
  return page

def planPages (bound : Bound) (frames : List Page.Frame) : Except GroupError (List DataPage) :=
  (frames.zipIdx 1).mapM fun (frame, ordinal) =>
    (planData bound frame).mapError (.header ordinal frame.header.start)

/-- The original selected chunk supplies the leading whole-body GZIP dictionary. -/
def checkGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError CheckedGroup :=
  Dictionary.Snappy.checkGroupWithCodec .gzip .chunk (Fallback.Gzip.readEntries limits)
    (planPages bound) limits.toDictionaryLimits bound index

abbrev GroupWire (limits : Limits) (bound : Bound) (index : Nat) (checked : CheckedGroup) : Prop :=
  Dictionary.Snappy.GroupWireWith limits.toDictionaryLimits bound index checked .gzip
    (Fallback.Gzip.readEntries limits) (fun page => planData bound page.frame = .ok page)

/-- The shared dictionary data decoder verifies the stored body before using
the V1 plan's codec and resolving the checked indices. -/
def decodePage (limits : Limits) (source : Bytes) (entries : Array Int32)
    (page : DataPage) (ordinal : Nat) : Except GroupError Slots :=
  (Dictionary.Snappy.decodePage limits.toDictionaryLimits source entries page ordinal).mapError .chunk

def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots :=
  Fallback.Gzip.readGroupWith (checkGroup limits bound) (decodePage limits) bound index

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Emit complete Date32 IPC after the checked source reaches EOF. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

/-- Original whole-body GZIP expansion, checked V1 levels and ordered
references into the signed dictionary entries. -/
structure PageWire (limits : Limits) (source : Bytes) (entries : Array Int32) (page : DataPage)
    (slots : Slots) : Prop where
  count : slots.length = page.params.numValues
  wire : ∃ header expanded layout sections, ∃ prepared : ScalarPage.Prepared, ∃ width runs indices,
    page.frame.value.kind = .dataV1 header ∧
    header.encoding = 8 ∧ header.numValues = page.params.numValues ∧
    page.params.schema.layout? = some layout ∧
    Fallback.Gzip.StoredMember source page.frame limits.scalar.compressedBytes limits.scalar.uncompressedBytes
      expanded ∧
    FlatPage.split layout limits.scalar.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
    FlatPage.readMask layout header.numValues limits.scalar.levels sections.definitions = .ok prepared.mask ∧
    prepared.scalars = sections.scalars ∧ slots.map Option.isSome = prepared.mask ∧
    prepared.scalars.toList = width :: runs ∧ width.toNat ≤ 32 ∧
    Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
    indices.map (fun index => entries[index]?) = (slots.filterMap id).map some

end Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V1
