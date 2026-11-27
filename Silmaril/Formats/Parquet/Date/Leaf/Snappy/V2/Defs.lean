module

public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec

/-! Opt-in selected Snappy PLAIN DATE data page V2. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Snappy.V2

abbrev Limits := Gzip.Limits
abbrev DataPage := Gzip.DataPage
abbrev CheckedGroup := Gzip.CheckedGroup

inductive GroupError where
  | plain (cause : Gzip.GroupError)
  | expectedV2 (ordinal offset : Nat)
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

/-- Keep the V2 compression flag and original level lengths. -/
def planData (bound : Bound) (frame : Page.Frame) (ordinal : Nat) :
    Except GroupError DataPage := do
  let .dataV2 header := frame.value.kind | throw (.expectedV2 ordinal frame.header.start)
  if header.encoding ≠ 0 then throw (.plain (Gzip.atFrame ordinal frame (.encoding header.encoding)))
  let some params := FlatScan.int32PageParameters bound.field frame.value |
    throw (.expectedV2 ordinal frame.header.start)
  return ⟨frame, { params with codec := Payload.Codec.snappy.id }⟩

/-- Reuse the original chunk extent, offsets, row count and both chunk caps. -/
def checkGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError CheckedGroup :=
  Gzip.checkGroupFor .snappy .plain (planData bound) limits bound index

/-- The original stored payload is CRC-checked before the V2 scalar decoder
separates the raw levels and resolves the compression flag. -/
def decodePage (limits : Limits) (source : Bytes) (page : DataPage) (ordinal : Nat) :
    Except GroupError Slots :=
  (Gzip.decodePage limits source page ordinal).mapError .plain

def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  let checked ← checkGroup limits bound index
  let pages ← checked.data.zipIdx.mapM fun (page, ordinal) =>
    decodePage limits bound.snapshot.bytes page ordinal
  return pages.flatten

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Publish a complete Date32 stream after the checked source reaches EOF. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

/-- The original selected PLAIN group includes the shared frame chain and row bound. -/
def GroupWire (limits : Limits) (bound : Bound) (index : Nat) (checked : CheckedGroup) : Prop :=
  Gzip.GroupWire limits bound index checked (fun page => ∃ ordinal, planData bound page.frame ordinal = .ok page)
    .snappy ∧ checked.selection.group.numRows.toNat ≤ limits.maxRows

/-- The flag selects one complete Snappy block or the literal value suffix. -/
def SuffixWire (frame : Page.Frame) (header : Page.DataV2) (stored plain : List UInt8) : Prop :=
  stored.length = frame.value.compressedSize - header.definitionBytes ∧
  plain.length = frame.value.uncompressedSize - header.definitionBytes ∧
  if header.isCompressed then
    Payload.Decodes (frame.value.uncompressedSize - header.definitionBytes) .snappy stored plain
  else plain = stored

/-- Signed nullable slots and their original checksummed page, levels, and value suffix. -/
def PageWire (limits : Limits) (source : Bytes) (page : DataPage) (slots : Slots) : Prop :=
  let frame := page.frame
  let stored := Page.Checksum.payloadBytes source frame
  ∃ (status : Page.Checksum.Status) (header : Page.DataV2) (layout : FlatPage.Layout)
    (definitions : Bytes) (suffix : List UInt8) (prepared : ScalarPage.Prepared) (words : List Int32),
    frame.value.kind = .dataV2 header ∧ header.encoding = 0 ∧
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
    definitions.length = header.definitionBytes ∧ stored.toList = definitions.toList ++ suffix ∧
    SuffixWire frame header suffix prepared.scalars.toList ∧
    ScalarPage.validate page.params limits.scalar stored = .ok layout ∧
    FlatPage.readMask layout header.numValues limits.scalar.levels definitions = .ok prepared.mask ∧
    Plain.decodeInt32 (prepared.mask.count true) prepared.scalars = .ok words ∧
    slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words ∧
    slots.length = header.numValues ∧ (slots.filterMap id).length + header.numNulls = header.numValues

/-- The checked group supplies the exact concatenation of its original pages. -/
def SlotsWire (limits : Limits) (bound : Bound) (index : Nat) (slots : Slots) : Prop :=
  ∃ checked pages, checkGroup limits bound index = .ok checked ∧
    GroupWire limits bound index checked ∧
    List.Forall₂ (PageWire limits bound.snapshot.bytes) checked.data pages ∧
    slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat

end Silmaril.Formats.Parquet.Date.Leaf.Snappy.V2
