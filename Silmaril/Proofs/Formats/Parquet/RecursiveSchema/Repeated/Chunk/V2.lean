module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Defs
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.Hybrid.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Page

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk

open Silmaril.Formats (Bytes)
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated (Leaf)
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (read : (first >>= next) = .ok value) : ∃ found, first = .ok found ∧ next found = .ok value := by
  cases first with
  | error => contradiction
  | ok result => exact ⟨result, rfl, read⟩

private theorem from_mapError {α ε δ : Type} {first : Except ε α} {wrap : ε → δ} {value : α}
    (read : first.mapError wrap = .ok value) : first = .ok value := by
  cases first <;> simp_all [Except.mapError]

public theorem v2_levels_wire {limits : Hybrid.Limits} {maximum count : Nat} {bytes : Bytes}
    {levels : List Nat} (read : readV2Levels limits maximum count bytes = .ok levels) :
    V2LevelWire limits maximum count bytes levels ∧ levels.length = count := by
  unfold readV2Levels at read
  split at read
  · rename_i omitted
    split at read
    · contradiction
    · rename_i empty
      split at read
      · contradiction
      · rename_i cap
        cases Except.ok.inj read
        exact ⟨.omitted omitted (Classical.not_not.mp empty) (by omega) (by omega),
          List.length_replicate⟩
  · rename_i positive
    have decoded := from_mapError read
    obtain ⟨width, cap, countCap, bytesCap, wire⟩ := Hybrid.decode_ok_iff.mp decoded
    exact ⟨.encoded positive width cap countCap bytesCap wire, Hybrid.decode_length decoded⟩

public theorem admitV2Page_wire {codec : ColumnCodec} {frame : Page.Frame} {remaining : Nat}
    {encoding : Int} {info : Page.DataV2}
    (read : admitV2Page codec frame remaining encoding = .ok info) :
    frame.value.kind = .dataV2 info ∧ info.encoding = encoding ∧ info.numValues ≤ remaining ∧
      (codec.v2 info = 0 → frame.value.uncompressedSize = frame.value.compressedSize) := by
  unfold admitV2Page at read
  split at read
  · rename_i original kind
    split at read
    · contradiction
    · rename_i encoding
      split at read
      · contradiction
      · rename_i sizes
        split at read
        · contradiction
        · rename_i count
          cases Except.ok.inj read
          exact ⟨kind, Classical.not_not.mp encoding, Nat.le_of_not_gt count,
            fun raw => Classical.byContradiction fun mismatch => sizes ⟨raw, mismatch⟩⟩
  · contradiction

private theorem bytesAt_exact {source : Bytes} {span : Footer.Span}
    (ordered : span.start ≤ span.stop) (inside : span.stop ≤ source.length) :
    source.slice? span.start (some span.stop) = some (bytesAt source span) := by
  apply Bytes.slice?_eq_some_iff.mpr
  refine ⟨ordered, inside, Bytes.ext ?_⟩
  rw [Bytes.toList_ofList]
  simp [bytesAt, Footer.fileBytes, Bytes.toList, ByteArray.data_extract]

private theorem v2_slices {limits : RecursiveSchema.Chunk.Limits} {source : Bytes} {frame : Page.Frame} {spans : Page.V2Spans}
    {checksum : Page.Checksum.Status}
    (checked : Page.Checksum.verify limits.maxBodyBytes source frame = .ok checksum)
    (split : frame.v2Spans = some spans) :
    ∀ span ∈ [spans.repetition, spans.definition, spans.values],
      source.slice? span.start (some span.stop) = some (bytesAt source span) := by
  have extent : Page.Checksum.PayloadWithin source frame := by
    cases checksum with
    | absent => exact (Page.Checksum.verify_absent_iff.mp checked).2.1
    | valid crc => exact (Page.Checksum.verify_valid_iff.mp checked).2.1
  have inside := extent.2.2.2
  obtain ⟨_, rep, repEnd, defn, defEnd, value, valueEnd⟩ := Page.v2Spans_bounds split
  intro span member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact bytesAt_exact (by omega) (by omega)

public theorem readV2SectionsWith_wire {limits : RecursiveSchema.Chunk.Limits}
    {maxRepetition maxDefinition : Nat} {source : Bytes}
    {frame : Page.Frame} {info : Page.DataV2} {sections : V2Sections}
    (read : readV2SectionsWith limits maxRepetition maxDefinition source frame info = .ok sections) :
    V2SectionsWireWith limits maxRepetition maxDefinition source frame info sections := by
  unfold readV2SectionsWith at read
  obtain ⟨checksum, checked, read⟩ := bind_ok read
  have verified := from_mapError checked
  cases split : frame.v2Spans with
  | none => simp [split] at read
  | some spans =>
    simp only [split] at read
    obtain ⟨reps, repRead, read⟩ := bind_ok read
    obtain ⟨defs, defRead, done⟩ := bind_ok read
    obtain ⟨repWire, repLength⟩ := v2_levels_wire (from_mapError repRead)
    obtain ⟨defWire, _⟩ := v2_levels_wire (from_mapError defRead)
    cases Except.ok.inj done
    exact ⟨⟨checksum, verified⟩, split, v2_slices verified split, repWire, defWire, repLength⟩

public theorem readV2Sections_wire {limits : Limits} {leaf : Leaf} {source : Bytes}
    {frame : Page.Frame} {info : Page.DataV2} {sections : V2Sections}
    (read : readV2Sections limits leaf source frame info = .ok sections) :
    V2SectionsWire limits leaf source frame info sections :=
  let wire := readV2SectionsWith_wire read
  ⟨wire.checksum, wire.spans, wire.slices, wire.repetitions, wire.definitions, wire.count⟩

public theorem checkV2Slots_wire {start : State} {info : Page.DataV2} {reps : List Nat}
    {decode : Unit → Except PageCause DecodedPage} {decoded : DecodedPage}
    (read : checkV2Slots info reps start decode = .ok decoded) :
    reps.head?.getD 0 = 0 ∧ reps.count 0 = info.numRows ∧ absentSlots decoded = info.numNulls ∧
      ∃ checked, decode () = .ok checked ∧ decoded = closeV2 checked := by
  unfold checkV2Slots at read
  dsimp only at read
  split at read
  · contradiction
  · rename_i first
    split at read
    · contradiction
    · rename_i rows
      obtain ⟨checked, readSlots, read⟩ := bind_ok read
      split at read
      · contradiction
      · rename_i nulls
        cases Except.ok.inj read
        exact ⟨Classical.not_not.mp first, Classical.not_not.mp rows, Classical.not_not.mp nulls,
          checked, readSlots, rfl⟩

public theorem readV2SuffixWith_wire {limits : Limits} {codec : ColumnCodec}
    {frame : Page.Frame} {info : Page.DataV2} {stored raw : Bytes} {signedExtent : Option Nat}
    (read : readV2SuffixWith limits codec frame info stored signedExtent = .ok raw) :
    v2LevelBytes info ≤ frame.value.compressedSize ∧ v2LevelBytes info ≤ frame.value.uncompressedSize ∧
      V2SuffixWire limits codec frame info stored raw := by
  unfold readV2SuffixWith at read
  dsimp only at read
  split at read
  · contradiction
  · rename_i extent
    have storedLevels : v2LevelBytes info ≤ frame.value.compressedSize := by omega
    have rawLevels : v2LevelBytes info ≤ frame.value.uncompressedSize := by omega
    refine ⟨storedLevels, rawLevels, ?_⟩
    split at read
    · rename_i uncompressed
      split at read
      · rename_i same
        cases Except.ok.inj read
        exact .raw uncompressed same
      · contradiction
    · rename_i notRaw
      have compressed : info.isCompressed = true := by
        cases flag : info.isCompressed
        · exact False.elim (notRaw (by simp [ColumnCodec.v2, ScalarPage.v2Codec, Payload.Codec.id, flag]))
        · rfl
      split at read
      · contradiction
      · rename_i bounded
        split at read
        · contradiction
        · obtain ⟨model, before, _, after, _⟩ := decodePayload_wire read
          exact .compressed compressed notRaw model before after (by omega) read

public theorem readV2Suffix_wire {limits : Limits} {codec : ColumnCodec} {leaf : Leaf}
    {frame : Page.Frame} {info : Page.DataV2} {stored raw : Bytes}
    (read : readV2Suffix limits codec leaf frame info stored = .ok raw) :
    v2LevelBytes info ≤ frame.value.compressedSize ∧ v2LevelBytes info ≤ frame.value.uncompressedSize ∧
      V2SuffixWire limits codec frame info stored raw :=
  readV2SuffixWith_wire read

public theorem decodeV2Page_wire {limits : Limits} {codec : ColumnCodec} {leaf : Leaf} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodeV2Page limits codec leaf source frame start remaining rowCeiling = .ok decoded) :
    V2PageWire limits codec leaf source frame start remaining rowCeiling decoded := by
  unfold decodeV2Page at read
  obtain ⟨info, header, read⟩ := bind_ok read
  obtain ⟨sections, sectionsRead, read⟩ := bind_ok read
  obtain ⟨suffix, suffixRead, read⟩ := bind_ok read
  have sectionsWire := readV2Sections_wire sectionsRead
  obtain ⟨storedExtent, rawExtent, suffixWire⟩ := readV2Suffix_wire suffixRead
  obtain ⟨first, rows, nulls, observed, slots, closed⟩ := checkV2Slots_wire read
  have slotWire := decodeSlots_wire slots
  have count := congrArg List.length (original_levels slotWire.slots).1
  simp only [List.length_map, sectionsWire.count] at count
  obtain ⟨kind, encoding, cap, sizes⟩ := admitV2Page_wire header
  obtain ⟨checksum, verified⟩ := sectionsWire.checksum
  exact ⟨info, sections.spans, sections.repetitions, sections.definitions, checksum, observed, suffix,
    kind, encoding, cap, sizes, storedExtent, rawExtent, verified, sectionsWire.spans, sectionsWire.slices,
    sectionsWire.repetitions, sectionsWire.definitions, suffixWire, first, rows, nulls,
    closed ▸ count, slotWire, closed⟩

public theorem decodeDataPage_wire {limits : Limits} {codec : ColumnCodec} {leaf : Leaf} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodeDataPage limits codec leaf source frame start remaining rowCeiling = .ok decoded) :
    DataPageWire limits codec leaf source frame start remaining rowCeiling decoded := by
  unfold decodeDataPage at read
  split at read
  · exact .v2 (decodeV2Page_wire read)
  · exact .v1 (decodeV1Page_wire read)
  · contradiction

public theorem v2_accounting {limits : Limits} {codec : ColumnCodec} {leaf : Leaf} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (wire : V2PageWire limits codec leaf source frame start remaining rowCeiling decoded) :
    ∃ info spans suffix, frame.value.kind = .dataV2 info ∧ frame.v2Spans = some spans ∧
      V2SuffixWire limits codec frame info (bytesAt source spans.values) suffix ∧
      decoded.levels.length = info.numValues ∧ decoded.words.length = info.numValues ∧
      decoded.levels.countP LevelSlot.startsRow = info.numRows ∧ absentSlots decoded = info.numNulls ∧
      suffix.length =
        (info.numValues - info.numNulls) * RecursiveSchema.Chunk.wordWidth leaf.kind ∧
      decoded.after.live = false := by
  obtain ⟨info, spans, reps, _, _, checked, suffix, kind, _, _, _, _, _, _, split, _, _, _, suffixWire,
    _, rows, nulls, count, decodedWire, closed⟩ := wire.original
  subst decoded
  change absentSlots checked = info.numNulls at nulls
  change checked.levels.length = info.numValues at count
  obtain ⟨words, exactBytes, wordCount, widths, presence, _⟩ := decodedWire.words
  have aligned : checked.words.length = info.numValues := by
    simpa only [List.length_map, count] using congrArg List.length presence
  have rowCount : checked.levels.countP LevelSlot.startsRow = info.numRows := by
    rw [← rows, ← (original_levels decodedWire.slots).1]
    simp only [List.count_eq_countP, List.countP_map]
    rfl
  have allSlots :
      (checked.levels.map LevelSlot.present).count true + absentSlots checked = checked.levels.length := by
    simpa [List.count_eq_countP, absentSlots, Function.comp_def] using
      (List.length_eq_countP_add_countP LevelSlot.present (l := checked.levels)).symm
  have signedCount : words.length = info.numValues - info.numNulls := by omega
  have suffixSize : suffix.length =
      (info.numValues - info.numNulls) * RecursiveSchema.Chunk.wordWidth leaf.kind := by
    rw [← Bytes.length_toList, exactBytes, List.length_flatten, List.map_eq_replicate_iff.mpr widths,
      List.sum_replicate_nat, signedCount]
  exact ⟨info, spans, suffix, kind, split, suffixWire, count, aligned, rowCount, nulls, suffixSize, rfl⟩

public theorem dataPage_counts {limits : Limits} {codec : ColumnCodec} {leaf : Leaf} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (wire : DataPageWire limits codec leaf source frame start remaining rowCeiling decoded) :
    start.slot + decoded.levels.length = decoded.after.slot ∧
      start.rows + decoded.levels.countP LevelSlot.startsRow = decoded.after.rows := by
  cases wire with
  | v1 v1 => exact v1_state_counts v1
  | v2 v2 =>
    obtain ⟨_, _, _, _, _, checked, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, slots, final⟩ :=
      v2.original
    subst decoded
    simpa only [closeV2] using slot_counts slots.slots

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk
