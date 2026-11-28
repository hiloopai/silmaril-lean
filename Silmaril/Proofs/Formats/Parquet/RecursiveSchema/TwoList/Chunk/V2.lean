module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Page
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Cursor
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk

open Silmaril.Formats (Bytes)
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk

private theorem checkV2Slots_wire {limits : Limits} {encoding : ValueEncoding} {plan : Plan} {info : Page.DataV2} {reps defs : List Nat}
    {suffix : Bytes} {start : State} {ceiling : Nat} {decoded : Decoded}
    (accepted : checkV2Slots limits plan info reps defs suffix start ceiling encoding = .ok decoded) :
    reps.head?.getD 0 = 0 ∧ reps.count 0 = info.numRows ∧ absentSlots decoded = info.numNulls ∧
      ∃ checked, DecodedWire limits plan ceiling start.close reps defs suffix checked encoding ∧ decoded = closeV2 checked := by
  unfold checkV2Slots at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  · rename_i first
    split at accepted
    · contradiction
    · rename_i rows
      obtain ⟨checked, slots, result⟩ := bind_ok accepted
      split at result
      · contradiction
      · rename_i nulls
        cases Except.ok.inj result
        exact ⟨Decidable.not_not.mp first, Decidable.not_not.mp rows, Decidable.not_not.mp nulls,
          checked, decodeSlots_wire slots, rfl⟩

public theorem decodeV2Page_wire {limits : Limits} {plan : Plan} {source : Bytes}
    {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded} {codec : Codec} {encoding : ValueEncoding}
    (accepted : decodeV2Page limits plan source frame start remaining ceiling codec encoding = .ok decoded) :
    V2PageWire limits plan source frame start remaining ceiling decoded codec encoding := by
  unfold decodeV2Page at accepted
  obtain ⟨info, header, rest⟩ := bind_ok accepted
  obtain ⟨sections, slices, rest⟩ := bind_ok rest
  obtain ⟨suffix, suffixRead, slots⟩ := bind_ok rest
  obtain ⟨kind, encoding, cap, _⟩ :=
    RecursiveSchema.Repeated.Chunk.admitV2Page_wire (from_mapError header)
  have sectionWire := RecursiveSchema.Repeated.Chunk.readV2SectionsWith_wire (from_mapError slices)
  obtain ⟨first, rows, nulls, checked, wire, rfl⟩ := checkV2Slots_wire slots
  have count : checked.levels.length = info.numValues := by
    simpa only [List.length_map, sectionWire.count] using congrArg List.length (original_levels wire.levels).1
  obtain ⟨_, levels, suffixWire⟩ := RecursiveSchema.Repeated.Chunk.readV2SuffixWith_wire (from_mapError suffixRead)
  have suffixLength : suffix.length = (RecursiveSchema.Repeated.Chunk.v2ValueBounds limits.payload frame info).expectedSize := by
    cases suffixWire with
    | raw _ length => exact length
    | compressed _ _ _ _ length _ _ => exact length
  have extent : RecursiveSchema.Repeated.Chunk.v2LevelBytes info + suffix.length = frame.value.uncompressedSize := by
    change suffix.length = frame.value.uncompressedSize - RecursiveSchema.Repeated.Chunk.v2LevelBytes info at suffixLength
    omega
  exact ⟨info, sections, suffix, checked, kind, encoding, cap, sectionWire, suffixWire, extent,
    first, rows, nulls, count, wire, rfl⟩

private theorem select_encoding_wire {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    {tag : Int} {encoding : ValueEncoding}
    (accepted : ValueEncoding.select dictionary tag = .ok encoding) : encoding.From dictionary := by
  unfold ValueEncoding.select at accepted
  split at accepted
  · cases dictionary with
    | none => contradiction
    | some original =>
      cases Except.ok.inj accepted
      exact .dictionary rfl
  · cases Except.ok.inj accepted
    exact .plain

public theorem decodeDataPage_wire {limits : Limits} {plan : Plan} {source : Bytes}
    {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded} {codec : Codec}
    {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    (accepted : decodeDataPage limits plan source frame start remaining ceiling codec dictionary = .ok decoded) :
    DataPageWire limits plan source frame start remaining ceiling decoded codec dictionary := by
  unfold decodeDataPage at accepted
  split at accepted
  · obtain ⟨encoding, selected, checked⟩ := bind_ok accepted
    exact .v1 (select_encoding_wire selected) (decodePage_wire checked)
  · obtain ⟨encoding, selected, checked⟩ := bind_ok accepted
    exact .v2 (select_encoding_wire selected) (decodeV2Page_wire checked)
  · contradiction
  · exact .v1 .plain (decodePage_wire accepted)

public theorem page_counts {limits : Limits} {plan : Plan} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining ceiling : Nat} {decoded : Decoded} {codec : Codec}
    {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    (wire : DataPageWire limits plan source frame start remaining ceiling decoded codec dictionary) :
    start.slots + decoded.levels.length = decoded.after.slots ∧
    start.rows + decoded.levels.countP Slot.startsRow = decoded.after.rows := by
  cases wire with
  | v1 _ first => exact v1_counts first
  | v2 _ second =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, checked, rfl⟩ := second.original
    simpa only [State.close, closeV2] using slot_counts checked.levels

public theorem v2_accounting {limits : Limits} {plan : Plan} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining ceiling : Nat} {decoded : Decoded} {codec : Codec} {encoding : ValueEncoding}
    (wire : V2PageWire limits plan source frame start remaining ceiling decoded codec encoding) :
    ∃ info spans suffix, frame.value.kind = .dataV2 info ∧ frame.v2Spans = some spans ∧
      RecursiveSchema.Repeated.Chunk.V2SuffixWire limits.payload codec.column frame info
        (RecursiveSchema.Repeated.Chunk.bytesAt source spans.values) suffix ∧
      decoded.levels.length = info.numValues ∧ decoded.words.length = info.numValues ∧
      decoded.levels.countP Slot.startsRow = info.numRows ∧ absentSlots decoded = info.numNulls ∧
      (encoding = .plain → suffix.length =
        (info.numValues - info.numNulls) * RecursiveSchema.Chunk.wordWidth plan.kind) ∧
      (decoded.levels.head?.map (·.repetition)).getD 0 = 0 ∧ decoded.after.live = .closed := by
  obtain ⟨info, sections, suffix, checked, kind, _, _, sectionWire, suffixWire, _, first, rows, nulls, count, decodedWire, rfl⟩ :=
    wire.original
  change absentSlots checked = info.numNulls at nulls
  change checked.levels.length = info.numValues at count
  have aligned : checked.words.length = info.numValues := by
    simpa only [List.length_map, count] using congrArg List.length decodedWire.aligned
  have rowCount : checked.levels.countP Slot.startsRow = info.numRows := by
    rw [← rows, List.count_eq_countP, repetition_count decodedWire.levels]
  have suffixSize (plain : encoding = .plain) : suffix.length =
      (info.numValues - info.numNulls) * RecursiveSchema.Chunk.wordWidth plan.kind := by
    subst encoding
    obtain ⟨words, exactBytes, wordCount, widths, _⟩ := decodedWire.words
    have allSlots : (checked.levels.map Slot.present).count true + absentSlots checked = checked.levels.length := by
      simpa [List.count_eq_countP, absentSlots, Function.comp_def] using
        (List.length_eq_countP_add_countP Slot.present (l := checked.levels)).symm
    have signedCount : words.length = info.numValues - info.numNulls := by omega
    rw [← Bytes.length_toList, exactBytes, List.length_flatten, List.map_eq_replicate_iff.mpr widths,
      List.sum_replicate_nat, signedCount]
  have starts : (checked.levels.head?.map (·.repetition)).getD 0 = 0 := by
    rw [← List.head?_map, (original_levels decodedWire.levels).1]
    exact first
  exact ⟨info, _, suffix, kind, sectionWire.spans, suffixWire, count, aligned, rowCount, nulls, suffixSize, starts, rfl⟩

public theorem v2_body {limits : Limits} {plan : Plan} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining ceiling : Nat} {decoded : Decoded} {codec : Codec} {encoding : ValueEncoding}
    (wire : V2PageWire limits plan source frame start remaining ceiling decoded codec encoding) :
    ∃ info spans, frame.value.kind = .dataV2 info ∧ frame.v2Spans = some spans ∧
      source.slice? frame.payload.start (some frame.payload.stop) = some (Page.Checksum.payloadBytes source frame) ∧
      (Page.Checksum.payloadBytes source frame).length = frame.value.compressedSize ∧
      spans.repetition.stop - spans.repetition.start = info.repetitionBytes ∧
      spans.definition.stop - spans.definition.start = info.definitionBytes ∧
      spans.values.stop - spans.values.start =
        frame.value.compressedSize - info.repetitionBytes - info.definitionBytes := by
  obtain ⟨info, sections, _, _, kind, _, _, sectionWire, _⟩ := wire.original
  obtain ⟨checksum, verified⟩ := sectionWire.checksum
  have extent : Page.Checksum.PayloadWithin source frame := by
    cases checksum with
    | absent => exact (Page.Checksum.verify_absent_iff.mp verified).2.1
    | valid crc => exact (Page.Checksum.verify_valid_iff.mp verified).2.1
  have width := extent.2.2.1
  obtain ⟨body, bodySize⟩ := Page.Checksum.payload_exact extent
  have split := sectionWire.spans
  have bounded : frame.payload.start + info.repetitionBytes + info.definitionBytes ≤ frame.payload.stop := by
    by_contra h
    simp [Page.Frame.v2Spans, kind, h] at split
  have spans := split
  simp [Page.Frame.v2Spans, kind, bounded] at spans
  refine ⟨info, sections.spans, kind, split, body, bodySize, ?_⟩
  rw [← spans]
  dsimp only
  omega

private theorem slots_start_closed {plan : Plan} {ceiling : Nat} {start stop : State}
    {reps defs : List Nat} {slots : List Slot}
    (wire : SlotsWire plan ceiling start reps defs slots stop) (closed : start.live = .closed) :
    (slots.head?.map (·.repetition)).getD 0 = 0 := by
  cases wire with
  | nil => rfl
  | @cons _ slot _ _ _ _ step _ =>
    have position : slot.position = .rowStart := by
      have admits := step.incoming
      rw [closed] at admits
      cases pos : slot.position <;> simp_all [Position.admits]
    exact (row_start step).mp (by simp [Slot.startsRow, position])

public theorem page_starts_closed {limits : Limits} {plan : Plan} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining ceiling : Nat} {decoded : Decoded} {codec : Codec}
    {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    (wire : DataPageWire limits plan source frame start remaining ceiling decoded codec dictionary)
    (closed : start.live = .closed) :
    (decoded.levels.head?.map (·.repetition)).getD 0 = 0 := by
  cases wire with
  | v1 _ first =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, slots, _⟩ := first.original
    exact slots_start_closed slots.levels closed
  | v2 _ second =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, starts, _⟩ := v2_accounting second
    exact starts

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk
