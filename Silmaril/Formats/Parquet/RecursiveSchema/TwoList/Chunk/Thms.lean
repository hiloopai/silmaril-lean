module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Cursor
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Page
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.V2

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk

open Silmaril.Formats (Bytes)

public section

theorem step_wire {plan : Plan} {ceiling rep defn : Nat} {start : State} {slot : Slot}
    (accepted : step plan ceiling start rep defn = .ok slot) :
    slot.repetition = rep ∧ slot.definition = defn ∧ StepWire plan ceiling start slot :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.step_wire accepted

/-- The new live depth is determined only by which original wrappers the
current definition reaches. An earlier inner List cannot stay live. -/
theorem StepWire.nextLive {plan : Plan} {ceiling : Nat} {start : State} {slot : Slot}
    (wire : StepWire plan ceiling start slot) :
    (start.consume slot).live =
      if plan.innerEmpty < slot.definition then .inner
      else if plan.outerEmpty < slot.definition then .outer else .closed :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.next_live wire

theorem StepWire.rowStart {plan : Plan} {ceiling : Nat} {start : State} {slot : Slot}
    (wire : StepWire plan ceiling start slot) : slot.startsRow = true ↔ slot.repetition = 0 :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.row_start wire

theorem StepWire.innerStart {plan : Plan} {ceiling : Nat} {start : State} {slot : Slot}
    (wire : StepWire plan ceiling start slot) (rep : slot.repetition = 1) :
    slot.position = .innerStart ∧ start.live ≠ .closed ∧ (start.consume slot).live ≠ .closed :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.inner_start wire rep

theorem StepWire.innerContinue {plan : Plan} {ceiling : Nat} {start : State} {slot : Slot}
    (wire : StepWire plan ceiling start slot) (rep : slot.repetition = 2) :
    slot.position = .innerContinue ∧ start.live = .inner ∧ (start.consume slot).live = .inner :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.inner_continue wire rep

theorem classify_wire {plan : Plan} {ceiling : Nat} {reps defs : List Nat}
    {start : State} {out : Classified} (accepted : classify plan ceiling start reps defs = .ok out) :
    SlotsWire plan ceiling start reps defs out.levels out.after :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.classify_wire accepted

theorem SlotsWire.originalLevels {plan : Plan} {ceiling : Nat} {reps defs : List Nat}
    {start stop : State} {slots : List Slot} (wire : SlotsWire plan ceiling start reps defs slots stop) :
    slots.map (·.repetition) = reps ∧ slots.map (·.definition) = defs :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.original_levels wire

theorem SlotsWire.repetitionCount {plan : Plan} {ceiling : Nat} {start stop : State}
    {reps defs : List Nat} {slots : List Slot} (wire : SlotsWire plan ceiling start reps defs slots stop) :
    reps.countP (· == 0) = slots.countP Slot.startsRow :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.repetition_count wire

/-- A successful V1 page binds the original header and stored body to its
decoded levels and ordered PLAIN words or dictionary lookups. -/
theorem decodePage_wire {limits : Limits} {plan : Plan} {source : Bytes}
    {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded} {codec : Codec} {encoding : ValueEncoding}
    (accepted : decodePage limits plan source frame start remaining ceiling codec encoding = .ok decoded) :
    PageWire limits plan source frame start remaining ceiling decoded codec encoding :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.decodePage_wire accepted

/-- Successful V2 decoding retains the original raw V2 sections, signed words and page counts. -/
theorem decodeV2Page_wire {limits : Limits} {plan : Plan} {source : Bytes}
    {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded} {codec : Codec} {encoding : ValueEncoding}
    (accepted : decodeV2Page limits plan source frame start remaining ceiling codec encoding = .ok decoded) :
    V2PageWire limits plan source frame start remaining ceiling decoded codec encoding :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.decodeV2Page_wire accepted

/-- Dispatch retains the checked witness for the original page version. -/
theorem decodeDataPage_wire {limits : Limits} {plan : Plan} {source : Bytes}
    {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded} {codec : Codec}
    {dictionary : Option Repeated.Chunk.Dictionary}
    (accepted : decodeDataPage limits plan source frame start remaining ceiling codec dictionary = .ok decoded) :
    DataPageWire limits plan source frame start remaining ceiling decoded codec dictionary :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.decodeDataPage_wire accepted

/-- The original V2 counts match the aligned slots, row starts and absent values. -/
theorem v2_accounting {limits : Limits} {plan : Plan} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining ceiling : Nat} {decoded : Decoded} {codec : Codec} {encoding : ValueEncoding}
    (wire : V2PageWire limits plan source frame start remaining ceiling decoded codec encoding) :
    ∃ info spans suffix, frame.value.kind = .dataV2 info ∧ frame.v2Spans = some spans ∧
      RecursiveSchema.Repeated.Chunk.V2SuffixWire limits.payload codec.column frame info
        (RecursiveSchema.Repeated.Chunk.bytesAt source spans.values) suffix ∧
      decoded.levels.length = info.numValues ∧ decoded.words.length = info.numValues ∧
      decoded.levels.countP Slot.startsRow = info.numRows ∧ absentSlots decoded = info.numNulls ∧
      (encoding = .plain → suffix.length =
        (info.numValues - info.numNulls) * RecursiveSchema.Chunk.wordWidth plan.kind) ∧
      (decoded.levels.head?.map (·.repetition)).getD 0 = 0 ∧ decoded.after.live = .closed :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.v2_accounting wire

/-- The original stored V2 body has exactly the advertised raw level and value extents. -/
theorem v2_body {limits : Limits} {plan : Plan} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining ceiling : Nat} {decoded : Decoded} {codec : Codec} {encoding : ValueEncoding}
    (wire : V2PageWire limits plan source frame start remaining ceiling decoded codec encoding) :
    ∃ info spans, frame.value.kind = .dataV2 info ∧ frame.v2Spans = some spans ∧
      source.slice? frame.payload.start (some frame.payload.stop) = some (Page.Checksum.payloadBytes source frame) ∧
      (Page.Checksum.payloadBytes source frame).length = frame.value.compressedSize ∧
      spans.repetition.stop - spans.repetition.start = info.repetitionBytes ∧
      spans.definition.stop - spans.definition.start = info.definitionBytes ∧
      spans.values.stop - spans.values.start =
        frame.value.compressedSize - info.repetitionBytes - info.definitionBytes :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.v2_body wire

/-- A page after a closed cursor cannot continue an outer or inner list. -/
theorem page_starts_closed {limits : Limits} {plan : Plan} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining ceiling : Nat} {decoded : Decoded} {codec : Codec}
    {dictionary : Option Repeated.Chunk.Dictionary}
    (wire : DataPageWire limits plan source frame start remaining ceiling decoded codec dictionary)
    (closed : start.live = .closed) :
    (decoded.levels.head?.map (·.repetition)).getD 0 = 0 :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.page_starts_closed wire closed

/-- Across the threaded cursor, either data page version must start a new
row after V2 whenever it has slots. -/
theorem V2PageWire.nextPageStarts {limits : Limits} {plan : Plan} {source : Bytes}
    {firstFrame nextFrame : Page.Frame} {start : State} {remaining nextRemaining ceiling : Nat}
    {decoded next : Decoded} {codec : Codec} {encoding : ValueEncoding}
    {dictionary : Option Repeated.Chunk.Dictionary} (first : V2PageWire limits plan source firstFrame start remaining ceiling decoded codec encoding)
    (following : DataPageWire limits plan source nextFrame decoded.after nextRemaining ceiling next codec dictionary) :
    (next.levels.head?.map (·.repetition)).getD 0 = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, closed⟩ := v2_accounting first
  exact page_starts_closed following closed

theorem ChainWire.counts {limits : Limits} {carrier : Carrier} {start stop : State}
    {frames : List Page.Frame} {pages : List ObservedPage}
    {dictionary : Option Repeated.Chunk.Dictionary}
    (wire : ChainWire limits carrier dictionary start frames pages stop) :
    start.slots + (pages.flatMap (·.decoded.levels)).length = stop.slots ∧
      start.rows + (pages.flatMap (·.decoded.levels)).countP Slot.startsRow = stop.rows :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.chain_counts wire

/-- The checked chunk covers the original bounded interval, carries state
from the closed group start, and meets both original footer counts. -/
theorem read_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Limits}
    {binding : Binding schema group} {out : Observation}
    (accepted : Chunk.read limits binding = .ok out) : Wire limits (carrierOf binding) out :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.read_wire accepted

/-- Every page of the checked chain uses the codec of its original column. -/
theorem Binding.codec_matches {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} (binding : Binding schema group) :
    (carrierOf binding).codec.column.id = binding.column.metadata.codec :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.codec_matches binding

/-- Both footer totals include every original page header, including a leading dictionary. -/
theorem chunk_bytes {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Limits}
    {binding : Binding schema group} {out : Observation} (wire : Wire limits (carrierOf binding) out) :
    let frames := out.frames
    (binding.span.start : Int) = binding.column.metadata.dictionaryPageOffset.getD binding.column.metadata.dataPageOffset ∧
    binding.column.metadata.totalCompressedSize = Int.ofNat (RecursiveSchema.Repeated.Chunk.storedChunkBytes frames) ∧
    binding.column.metadata.totalUncompressedSize = Int.ofNat (RecursiveSchema.Repeated.Chunk.rawChunkBytes frames) :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.chunk_bytes wire

/-- The first original frame and declared first data offset bind a local dictionary. -/
theorem Wire.dictionary_anchors {limits : Limits} {carrier : Carrier} {out : Observation}
    {dictionary : Repeated.Chunk.Dictionary}
    (wire : Wire limits carrier out) (selected : out.dictionary = some dictionary) :
    dictionary.codec.column = carrier.codec.column ∧
    carrier.metadata.dictionaryPageOffset = some (Int.ofNat carrier.span.start) ∧
    carrier.metadata.dataPageOffset = Int.ofNat dictionary.frame.payload.stop ∧
    Page.readPage limits.framing carrier.source carrier.span carrier.span.start = .ok dictionary.frame ∧
    Repeated.Chunk.DictionaryContentsWire limits.payload carrier.plan.kind carrier.source dictionary :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.dictionary_anchors wire selected

/-- The first original data page starts exactly at the declared data offset. -/
theorem Wire.dictionary_first_data {limits : Limits} {carrier : Carrier} {out : Observation}
    {dictionary : Repeated.Chunk.Dictionary}
    (wire : Wire limits carrier out) (selected : out.dictionary = some dictionary) :
    ∃ page, out.pages.head? = some page ∧
      carrier.metadata.dataPageOffset = Int.ofNat page.frame.header.start :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.dictionary_first_data wire selected

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk
