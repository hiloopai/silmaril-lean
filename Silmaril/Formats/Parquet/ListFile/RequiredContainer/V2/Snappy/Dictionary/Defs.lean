module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Defs
public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Defs
public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Defs

/-! One leading signed PLAIN dictionary and RLE_DICTIONARY Data Page V2
frames per required LIST chunk. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary

open Silmaril.Relational
open ListPage (Event Row)
open RequiredContainer (Checked SectionsWireUsing)
open ListFile.Multi.Snappy (Budget readGroupsWith)
open ListFile.Multi.Snappy.DictionaryV1 (LookupWire readValues)
open V2 (rowStarts missingSlots)

abbrev Limits := ListFile.Multi.Snappy.DictionaryV1.Limits
abbrev FrameError := ListFile.Multi.Snappy.DictionaryV1.FrameError
abbrev GroupError := ListFile.Multi.Snappy.DictionaryV1.GroupError

def bodyLimits (limits : Limits) : Snappy.Limits :=
  { maxStoredPageBytes := limits.snappy.maxStoredPageBytes }

/-- Resolve the original dictionary against definition-two slots only, after
checking the full stored V2 body and preparing its flag-selected suffix. -/
def readFrame (limits : Limits) (checked : Checked) (entries : Array Int32)
    (budget : Budget) (frame : Page.Frame) : Except FrameError (List Event) := do
  let .dataV2 info := frame.value.kind | throw (.v2 (.page .pageKind))
  if info.encoding ≠ 8 then return ← throw (.dataEncoding info.encoding)
  if budget.slots < info.numValues then return ← throw (.slotBudget budget.slots info.numValues)
  if budget.expanded < frame.value.uncompressedSize then
    return ← throw (.expandedBudget budget.expanded frame.value.uncompressedSize)
  if checked.limits.page.maxRows < info.numRows then return ← throw (.page .rowLimit)
  let sections ← (Snappy.readSections (bodyLimits limits) checked frame info).mapError .v2
  let events ← RequiredContainer.decodeSectionsUsing ListFile.Multi.Snappy.DictionaryV1.FrameError.page (readValues limits entries) checked.limits.page
    info.numValues sections.repetition sections.definition sections.scalars
  (ListFile.Multi.Snappy.checkV2Counts info events).mapError .v2
  pure events

structure FrameWire (limits : Limits) (checked : Checked) (entries : Array Int32)
    (frame : Page.Frame) (events : List Event) : Prop where
  data : ∃ info sections,
    frame.value.kind = .dataV2 info ∧ info.encoding = 8 ∧ info.numRows ≤ checked.limits.page.maxRows ∧
    Snappy.StoredWire (bodyLimits limits) checked frame info sections ∧
    SectionsWireUsing (readValues limits entries) info.numValues sections.repetition
      sections.definition sections.scalars events ∧
    ListFile.Multi.startsWithinRow events = false ∧ rowStarts events = info.numRows ∧
    missingSlots events = info.numNulls ∧
    LookupWire limits entries (info.numValues - info.numNulls) sections.scalars
      (events.filterMap (fun event => event.wire.2.2))

def readGroup (limits : Limits) : ListFile.Multi.Snappy.GroupReaderFor GroupError .required :=
  ListFile.Multi.Snappy.DictionaryV1.readGroupUsing limits (fun checked _ => readFrame limits checked)

abbrev GroupWire (limits : Limits) :=
  ListFile.Multi.Snappy.DictionaryV1.GroupWireUsing limits
    (fun (checked : Checked) _ => FrameWire limits checked)

abbrev SourceError := RequiredContainer.SourceError GroupError
abbrev Result := RequiredContainer.Result GroupError

def convert (limits : Limits) (source : Bytes) : Result :=
  match RequiredContainer.openFile limits.snappy.parquet.file source with
  | .error cause => ⟨.error (.openFailure cause), .error (.source (.openFailure cause))⟩
  | .ok checked =>
    let (groups, outcome) := readGroupsWith RequiredContainer.SourceError.groupFailure (readGroup limits) checked
      limits.snappy.maxExpandedBytes (List.range checked.snapshot.groupCount)
    let batches := groups.map (AlignedColumns.ofRows ∘ RequiredContainer.rowsOf checked)
    match outcome with
    | .error cause => ⟨.ok ⟨RequiredContainer.schema checked, ⟨batches, .readError cause⟩⟩, .error (.source cause)⟩
    | .ok _ => ⟨.ok ⟨RequiredContainer.schema checked, ⟨batches, .eos⟩⟩,
        (Arrow.ListInt32.Stream.Writer.emitFor false limits.snappy.ipc
          (RequiredContainer.fieldOf checked) groups).mapError .writer⟩

structure Readback (limits : Limits) (source : Bytes) (wire : KBytes) : Prop where
  data : ∃ checked groups costs left decoded size,
    RequiredContainer.openFile limits.snappy.parquet.file source = .ok checked ∧
    ListFile.OpenWire limits.snappy.parquet.file source checked ∧
    readGroupsWith RequiredContainer.SourceError.groupFailure (readGroup limits) checked limits.snappy.maxExpandedBytes
      (List.range checked.snapshot.groupCount) = (groups, .ok left) ∧
    List.Forall₂ (fun ordinal (batch : List Row × Nat) => GroupWire limits checked ordinal batch.1 batch.2)
      (List.range checked.snapshot.groupCount) (groups.zip costs) ∧
    costs.length = groups.length ∧ costs.sum + left = limits.snappy.maxExpandedBytes ∧
    (convert limits source).trace = .ok ⟨RequiredContainer.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ RequiredContainer.rowsOf checked), .eos⟩⟩ ∧
    Arrow.ListInt32.Stream.readFor false limits.snappy.ipc wire = .ok decoded ∧
    Arrow.ListInt32.Stream.Writer.Agrees (RequiredContainer.fieldOf checked) groups decoded ∧
    wire.wf = true ∧
    Arrow.readEnvelope limits.snappy.ipc.ipc wire 0 = .ok (.metadata size) ∧
    Arrow.ListInt32.readSchemaFor false limits.snappy.ipc.ipc (wire.slice 8 size) = .ok (RequiredContainer.fieldOf checked) ∧
    Arrow.ListInt32.Stream.BatchesWire limits.snappy.ipc wire limits.snappy.ipc.ipc.batches 0 0 (8 + size) decoded.batches ∧
    Arrow.ListInt32.Stream.checkParents false decoded.batches = .ok ()

end Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Dictionary
