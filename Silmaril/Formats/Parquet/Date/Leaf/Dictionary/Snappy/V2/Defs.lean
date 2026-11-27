module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Snappy.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec

/-! Explicit strict Snappy DATE V2 profiles for groups with a PLAIN dictionary. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2

open DictionaryChunk (DataPage)

inductive Profile where
  | dictionaryOnly
  | fallback
  deriving DecidableEq, Repr

def Profile.admits : Profile → Int → Bool
  | .dictionaryOnly => (· == 8)
  | .fallback => Date.Leaf.Fallback.Snappy.admits

inductive HeaderError where
  | expectedV2
  | data (cause : Snappy.PageError)
  deriving DecidableEq, Repr

inductive GroupError where
  | chunk (cause : Snappy.GroupError)
  | header (ordinal offset : Nat) (cause : HeaderError)
  | sequence (cause : Date.Leaf.Fallback.GroupError)
  | decode (cause : Date.Leaf.Fallback.Snappy.GroupError)
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

/-- Select original V2 data headers before applying the existing encoding check. -/
def planData (profile : Profile) (bound : Bound) (frame : Page.Frame) :
    Except HeaderError DataPage :=
  match frame.value.kind with
  | .dataV2 _ => (Snappy.planDataWith profile.admits bound frame).mapError .data
  | _ => .error .expectedV2

def atHeader (ordinal : Nat) (frame : Page.Frame) : HeaderError → GroupError :=
  .header ordinal frame.header.start

/-- Apply only the caller's strict plan to the data frames after the leading dictionary. -/
def planPages (profile : Profile) (bound : Bound) (frames : List Page.Frame) :
    Except GroupError (List DataPage) :=
  match profile with
  | .dictionaryOnly =>
    (frames.zipIdx 1).mapM fun (frame, ordinal) =>
      (planData .dictionaryOnly bound frame).mapError (atHeader ordinal frame)
  | .fallback =>
    Date.Leaf.Fallback.planPagesWith (planData .fallback bound) atHeader id .sequence frames

def checkGroup (profile : Profile) (limits : Limits) (bound : Bound) (index : Nat) :
    Except GroupError CheckedGroup :=
  Snappy.checkGroupWith .chunk (planPages profile bound) limits bound index

/-- Decode the checked group's original CRC-bearing pages with the shared Snappy reader. -/
def decodePage (limits : Limits) (source : Bytes) (entries : Array Int32) (page : DataPage)
    (ordinal : Nat) : Except GroupError Slots :=
  (Date.Leaf.Fallback.Snappy.decodePage limits source entries page ordinal).mapError .decode

def decodeGroup (limits : Limits) (source : Bytes) (checked : CheckedGroup) : Except GroupError Slots := do
  let entries := checked.entries.toArray
  let pages ← (checked.data.zipIdx 1).mapM fun (page, ordinal) => decodePage limits source entries page ordinal
  return pages.flatten

def readGroup (profile : Profile) (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots :=
  checkGroup profile limits bound index >>= decodeGroup limits bound.snapshot.bytes

def trace (profile : Profile) (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup profile limits bound) .groupFailure

def readAll (profile : Profile) (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace profile limits bound⟩

/-- Emit native Date32 IPC only after the selected profile reaches source EOS. -/
def toIpc (profile : Profile) (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace profile limits bound)

def Phase : Profile → List DataPage → Prop
  | .dictionaryOnly, data => ∀ page ∈ data, page.params.encoding = 8
  | .fallback, data => Date.Leaf.Fallback.Ordered data

def GroupWire (profile : Profile) (limits : Limits) (bound : Bound) (index : Nat)
    (checked : CheckedGroup) : Prop :=
  Snappy.GroupWireWith limits bound index checked .snappy (Snappy.readEntries limits)
    (fun page => planData profile bound page.frame = .ok page) ∧
    checked.data ≠ [] ∧ Phase profile checked.data

/-- The original leading PLAIN dictionary is one bounded Snappy block. -/
def DictionaryWire (limits : Limits) (source : Bytes) (frame : Page.Frame) (entries : List Int32) : Prop :=
  let stored := Page.Checksum.payloadBytes source frame
  let bounds := Snappy.dictionaryBounds limits frame
  ∃ (header : Page.Dictionary) (status : Page.Checksum.Status) (expanded : List UInt8),
    frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧ header.numValues ≤ limits.maxEntries ∧
    Page.Checksum.verify bounds.compressedLimit source frame = .ok status ∧
    source.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ bounds.compressedLimit ∧
    (match status with
     | .absent => frame.value.crc = none
     | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
    Payload.Decodes frame.value.uncompressedSize .snappy stored.toList expanded ∧
    expanded.length = frame.value.uncompressedSize ∧ expanded.length ≤ bounds.outputLimit ∧
    Plain.decodeInt32 header.numValues (Bytes.ofList expanded) = .ok entries ∧ entries.length = header.numValues

def ValuesWire (tag : Int) (entries : Array Int32) (prepared : ScalarPage.Prepared) (slots : Slots) : Prop :=
  (tag = 8 ∧ ∃ (width : UInt8) (runs : List UInt8) (indices : List Nat),
    prepared.scalars.toList = width :: runs ∧ width.toNat ≤ 32 ∧
    Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
    indices.map (fun index => entries[index]?) = (slots.filterMap id).map some) ∨
  (tag = 0 ∧ Plain.decodeInt32 (prepared.mask.count true) prepared.scalars = .ok (slots.filterMap id))

/-- The retained V2 header fixes the raw levels and the exact flag-selected
suffix. The suffix supplies wire-order references or signed PLAIN words. -/
def PageWire (limits : Limits) (source : Bytes) (entries : Array Int32) (page : DataPage) (slots : Slots) : Prop :=
  slots.length = page.params.numValues ∧
  let frame := page.frame
  let stored := Page.Checksum.payloadBytes source frame
  ∃ (header : Page.DataV2) (status : Page.Checksum.Status) (layout : FlatPage.Layout)
    (levels : Bytes) (suffix : List UInt8) (prepared : ScalarPage.Prepared),
    frame.value.kind = .dataV2 header ∧
    Page.Checksum.verify limits.scalar.compressedBytes source frame = .ok status ∧
    source.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.scalar.compressedBytes ∧
    frame.value.uncompressedSize ≤ limits.scalar.uncompressedBytes ∧
    (match status with
     | .absent => frame.value.crc = none
     | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
    header.numRows = header.numValues ∧ header.repetitionBytes = 0 ∧
    header.definitionBytes ≤ frame.value.compressedSize ∧
    header.definitionBytes ≤ frame.value.uncompressedSize ∧
    header.definitionBytes ≤ limits.scalar.levels.bytes ∧
    levels.length = header.definitionBytes ∧ stored.toList = levels.toList ++ suffix ∧
    FlatPage.readMask layout header.numValues limits.scalar.levels levels = .ok prepared.mask ∧
    ScalarPage.ExactPayload (frame.value.compressedSize - header.definitionBytes)
      (frame.value.uncompressedSize - header.definitionBytes)
      (if header.isCompressed then Payload.Codec.snappy.id else Payload.Codec.uncompressed.id)
      suffix prepared.scalars.toList ∧
    ValuesWire header.encoding entries prepared slots ∧ slots.map Option.isSome = prepared.mask ∧
    slots.length = header.numValues ∧ (slots.filterMap id).length + header.numNulls = header.numValues

def SlotsWire (profile : Profile) (limits : Limits) (bound : Bound) (index : Nat) (slots : Slots) : Prop :=
  ∃ checked pages, checkGroup profile limits bound index = .ok checked ∧
    GroupWire profile limits bound index checked ∧
    DictionaryWire limits bound.snapshot.bytes checked.dictionary checked.entries ∧
    List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages ∧
    slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat

end Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2
