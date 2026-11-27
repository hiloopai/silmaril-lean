module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Defs

/-! A leading PLAIN signed dictionary and V2 dictionary data pages in the
canonical Snappy nullable INT32 LIST chunk. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2

open DictionaryV1 (readValues LookupWire)
open Snappy (Budget)
open ListPage (Event Row)

/-- Verify the full stored V2 body, split the two raw level extents and
decode the flag-selected dictionary-index suffix. -/
def readFrame (limits : DictionaryV1.Limits) (checked : ListFile.Checked)
    (entries : Array Int32) (budget : Budget) (frame : Page.Frame) : Except DictionaryV1.FrameError (List Event) := do
  let .dataV2 info := frame.value.kind | throw (.v2 (.page .pageKind))
  if info.encoding ≠ 8 then return ← throw (.dataEncoding info.encoding)
  if budget.slots < info.numValues then return ← throw (.slotBudget budget.slots info.numValues)
  if budget.expanded < frame.value.uncompressedSize then
    return ← throw (.expandedBudget budget.expanded frame.value.uncompressedSize)
  let source := checked.snapshot.bytes
  let _ ← (Page.Checksum.verify limits.snappy.maxStoredPageBytes source frame).mapError .checksum
  let sections ← (Snappy.prepareV2 limits.snappy checked frame info
    (Page.Checksum.payloadBytes source frame)).mapError .v2
  let events ← ListPage.decodeSectionsUsing DictionaryV1.FrameError.page (readValues limits entries) checked.limits.page
    info.numValues sections.repetition sections.definition sections.scalars
  (Snappy.checkV2Counts info events).mapError .v2
  pure events

structure FrameWire (limits : DictionaryV1.Limits) (checked : ListFile.Checked) (entries : Array Int32)
    (frame : Page.Frame) (events : List Event) : Prop where
  data : ∃ status stored info sections spans,
    Page.Checksum.verify limits.snappy.maxStoredPageBytes checked.snapshot.bytes frame = .ok status ∧
    checked.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.snappy.maxStoredPageBytes ∧
    frame.value.kind = .dataV2 info ∧ info.encoding = 8 ∧ frame.v2Spans = some spans ∧
    spans.repetition.stop - spans.repetition.start = info.repetitionBytes ∧
    spans.definition.stop - spans.definition.start = info.definitionBytes ∧
    Snappy.V2BodyWire checked frame info stored sections ∧
    ListPage.SectionsWireUsing (readValues limits entries)
      info.numValues sections.repetition sections.definition sections.scalars events ∧
    Multi.startsWithinRow events = false ∧ Snappy.pageRows events = info.numRows ∧
    Snappy.pageNulls events = info.numNulls ∧
    LookupWire limits entries (info.numValues - info.numNulls) sections.scalars
      (events.filterMap (fun event => event.wire.2.2))

def dataReader (limits : DictionaryV1.Limits) : DictionaryV1.DataReader :=
  fun checked _ => readFrame limits checked

def dataWitness (limits : DictionaryV1.Limits) : DictionaryV1.DataWitness :=
  fun checked _ => FrameWire limits checked

def readGroup (limits : DictionaryV1.Limits) (checked : ListFile.Checked) (ordinal expanded : Nat) :
    Except DictionaryV1.GroupError (List Row × Nat) :=
  DictionaryV1.readGroupUsing limits (dataReader limits) checked ordinal expanded

abbrev GroupWire (limits : DictionaryV1.Limits) :=
  DictionaryV1.GroupWireUsing limits (dataWitness limits)

def convert (limits : DictionaryV1.Limits) (source : Bytes) : Snappy.ResultWith DictionaryV1.SourceError DictionaryV1.Error :=
  Snappy.convertWith DictionaryV1.errors limits.snappy (readGroup limits) source

abbrev Readback (limits : DictionaryV1.Limits) (source : Bytes) (wire : KBytes) :=
  Snappy.ReadbackWith DictionaryV1.errors limits.snappy (readGroup limits) (GroupWire limits) source wire

end Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2
