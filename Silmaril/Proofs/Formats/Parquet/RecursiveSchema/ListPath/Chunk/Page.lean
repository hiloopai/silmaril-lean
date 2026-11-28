module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Levels
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Sections

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk

open Silmaril.Formats
open Parquet
open Parquet.RecursiveSchema.ListPath
open Parquet.RecursiveSchema.ListPath.Chunk

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {out : β}
    (read : (first >>= next) = .ok out) : ∃ found, first = .ok found ∧ next found = .ok out := by
  cases first with
  | error => contradiction
  | ok result => exact ⟨result, rfl, read⟩

private theorem from_mapError {α ε δ : Type} {first : Except ε α} {wrap : ε → δ} {out : α}
    (read : first.mapError wrap = .ok out) : first = .ok out := by
  cases first with
  | error => simp [Except.mapError] at read
  | ok => simpa only [Except.mapError, Except.ok.injEq] using read

private theorem checked_extent {cap : Nat} {source : Bytes} {frame : Page.Frame}
    {status : Page.Checksum.Status}
    (checked : Page.Checksum.verify cap source frame = .ok status) :
    Page.Checksum.PayloadWithin source frame := by
  cases status with
  | absent => exact (Page.Checksum.verify_absent_iff.mp checked).2.1
  | valid => exact (Page.Checksum.verify_valid_iff.mp checked).2.1

private theorem read_values_wire {encoding : ValueEncoding} {limits : Limits}
    {kind : RecursiveSchema.Kind} {count : Nat} {suffix : Bytes}
    {words : List RecursiveSchema.Chunk.Word}
    (accepted : encoding.read limits kind count suffix = .ok words) :
    encoding.Wire limits kind count suffix words := by
  cases encoding with
  | plain =>
    obtain ⟨_, physical, extent, count, widths, values⟩ :=
      Plain.decodeFixedWidth_ok_iff.mp (from_mapError accepted)
    exact ⟨physical, extent, count, widths, values⟩
  | dictionary _ => exact DictionaryIndex.readValues_wire (from_mapError accepted)

private theorem decodeSlots_wire {plan : Plan} {wrappers : List Nat} {spans : Sections}
    {start : State} {ceiling : Nat} {reps defs : List Nat} {suffix : Bytes} {decoded : Decoded}
    {limits : Limits} {encoding : ValueEncoding}
    (accepted : decodeSlots plan wrappers spans start ceiling reps defs suffix limits encoding = .ok decoded) :
    decoded.sections = spans ∧ SlotsWire plan wrappers start ceiling reps defs suffix decoded limits encoding := by
  unfold decodeSlots at accepted
  obtain ⟨stop, scanned, accepted⟩ := bind_ok accepted
  obtain ⟨words, wordsRead, accepted⟩ := bind_ok accepted
  obtain ⟨aligned, alignedRead, done⟩ := bind_ok accepted
  cases Except.ok.inj done
  have states := scan_wire (from_mapError scanned)
  have alignedWire := FlatPage.reconstruct_ok_iff.mp (from_mapError alignedRead)
  exact ⟨rfl, aligned, states, alignedWire.2.symm ▸ read_values_wire wordsRead, alignedWire.1, rfl⟩

private theorem v1_body_slice {limits : Limits} {codec : Codec} {source body : Bytes} {frame : Page.Frame}
    (read : RecursiveSchema.Repeated.Chunk.readV1Body limits.payload codec.column source frame = .ok body) :
    let input := codec.v1Source source frame body
    input.bytes.slice? input.span.start (some input.span.stop) = some body := by
  cases codec with
  | uncompressed =>
    obtain ⟨_, checked, done⟩ := bind_ok read
    cases Except.ok.inj done
    exact (Page.Checksum.payload_exact (checked_extent (from_mapError checked))).1
  | snappy | gzip | zstd | lz4Raw =>
    change body.slice? 0 (some body.length) = some body
    apply Bytes.slice?_eq_some_iff.mpr
    refine ⟨by simp, by simp, ?_⟩
    simp only [Option.getD_some, Nat.sub_zero, List.drop_zero]
    rw [← Bytes.length_toList, List.take_length, Bytes.ofList_toList]

public theorem decodePage_wire {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {encoding : ValueEncoding}
    (accepted : decodePage limits plan wrappers source frame start remaining ceiling codec encoding = .ok decoded) :
    PageWire limits plan wrappers source frame start remaining ceiling decoded codec encoding := by
  unfold decodePage at accepted
  obtain ⟨info, header, accepted⟩ := bind_ok accepted
  obtain ⟨body, bodyRead, accepted⟩ := bind_ok accepted
  obtain ⟨reps, repRead, accepted⟩ := bind_ok accepted
  obtain ⟨defs, defRead, slots⟩ := bind_ok accepted
  have admitted := from_mapError header
  unfold RecursiveSchema.Repeated.Chunk.admitPage at admitted
  obtain ⟨kind, encodings, cap, sizes⟩ := RecursiveSchema.Chunk.admitPageWith_wire (from_mapError admitted)
  have decodedBody := from_mapError bodyRead
  have bodyWire := RecursiveSchema.Repeated.Chunk.readV1Body_wire sizes decodedBody
  obtain ⟨repWire, repCount⟩ := RecursiveSchema.Repeated.Chunk.readLevels_wire (from_mapError repRead)
  obtain ⟨defWire, defCount⟩ := RecursiveSchema.Repeated.Chunk.readLevels_wire (from_mapError defRead)
  have parts := sections_wire (v1_body_slice decodedBody) repWire defWire
  obtain ⟨layout, values⟩ := decodeSlots_wire slots
  exact ⟨info, body, reps, defs, kind, encodings, cap, bodyWire, layout.symm ▸ parts, repCount, defCount, values⟩

public theorem decodeV2Page_wire {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {encoding : ValueEncoding}
    (accepted : decodeV2Page limits plan wrappers source frame start remaining ceiling codec encoding = .ok decoded) :
    V2PageWire limits plan wrappers source frame start remaining ceiling decoded codec encoding := by
  unfold decodeV2Page at accepted
  obtain ⟨info, header, accepted⟩ := bind_ok accepted
  obtain ⟨parts, sections, accepted⟩ := bind_ok accepted
  obtain ⟨suffix, suffixRead, accepted⟩ := bind_ok accepted
  obtain ⟨checked, counted, done⟩ := bind_ok accepted
  cases Except.ok.inj done
  obtain ⟨kind, encoding, cap, sizes⟩ := RecursiveSchema.Repeated.Chunk.admitV2Page_wire (from_mapError header)
  have rawLevels := RecursiveSchema.Repeated.Chunk.readV2SectionsWith_wire (from_mapError sections)
  obtain ⟨_, bounded, suffixWire⟩ := RecursiveSchema.Repeated.Chunk.readV2SuffixWith_wire (from_mapError suffixRead)
  have length : suffix.length = (RecursiveSchema.Repeated.Chunk.v2ValueBounds limits.payload frame info).expectedSize := by
    cases suffixWire with
    | raw _ length => exact length
    | compressed _ _ _ _ length _ _ => exact length
  have extent : RecursiveSchema.Repeated.Chunk.v2LevelBytes info + suffix.length = frame.value.uncompressedSize := by
    change suffix.length = frame.value.uncompressedSize - RecursiveSchema.Repeated.Chunk.v2LevelBytes info at length
    omega
  obtain ⟨first, rows, nulls, slots⟩ := RecursiveSchema.Repeated.Chunk.checkV2Counts_wire counted
  obtain ⟨layout, values⟩ := decodeSlots_wire slots
  exact ⟨info, parts, suffix, checked, kind, encoding, cap, sizes, rawLevels, suffixWire, extent,
    first, rows, nulls, layout, values, rfl⟩

private theorem selected_from {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    {tag : Int} {encoding : ValueEncoding} (read : ValueEncoding.select dictionary tag = .ok encoding) :
    encoding.From dictionary := by
  unfold ValueEncoding.select at read
  split at read
  · cases dictionary with
    | none => contradiction
    | some table =>
      cases Except.ok.inj read
      exact .dictionary rfl
  · cases Except.ok.inj read
    exact .plain

public theorem decodeDataPage_wire {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    (accepted : decodeDataPage limits plan wrappers source frame start remaining ceiling codec dictionary = .ok decoded) :
    DataPageWire limits plan wrappers source frame start remaining ceiling decoded codec dictionary := by
  unfold decodeDataPage at accepted
  split at accepted
  · obtain ⟨_, selected, read⟩ := bind_ok accepted
    exact .v1 (selected_from selected) (decodePage_wire read)
  · obtain ⟨_, selected, read⟩ := bind_ok accepted
    exact .v2 (selected_from selected) (decodeV2Page_wire read)
  · contradiction
  · exact .v1 .plain (decodePage_wire accepted)

private theorem slot_counts {plan : Plan} {wrappers : List Nat} {start : State} {ceiling : Nat}
    {reps defs : List Nat} {suffix : Bytes} {decoded : Decoded}
    {limits : Limits} {encoding : ValueEncoding}
    (wire : SlotsWire plan wrappers start ceiling reps defs suffix decoded limits encoding)
    (balanced : reps.length = defs.length) :
    decoded.atoms.length = reps.length ∧ decoded.atoms.countP (·.repetition == 0) = reps.count 0 ∧
      start.slots + decoded.atoms.length = decoded.after.slots ∧
      start.rows + decoded.atoms.countP (·.repetition == 0) = decoded.after.rows := by
  obtain ⟨aligned, scanned, _, maskWire, atomsWire⟩ := wire.original
  have len : aligned.length = (reps.zip defs).length := by
    have maskCount := congrArg List.length maskWire
    simpa [mask, balanced] using maskCount
  have axes := (atoms_axes len).1
  have count : decoded.atoms.length = reps.length := by
    simpa [atomsWire, balanced] using congrArg List.length axes
  have rows : decoded.atoms.countP (·.repetition == 0) =
      (reps.zip defs).countP (fun level => level.1 == 0) := by
    simpa [atomsWire, Function.comp_def] using congrArg (List.countP fun level : Nat × Nat => level.1 == 0) axes
  have originalRows : (reps.zip defs).countP (fun level => level.1 == 0) = reps.count 0 := by
    simpa [List.count_eq_countP, Function.comp_def] using
      congrArg (List.countP (· == 0)) (List.map_fst_zip (Nat.le_of_eq balanced))
  have ⟨slots, afterRows⟩ := scan_counts scanned
  exact ⟨count, rows.trans originalRows, by simpa [count, balanced] using slots, rows ▸ afterRows⟩

public theorem page_counts {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {encoding : ValueEncoding}
    (wire : PageWire limits plan wrappers source frame start remaining ceiling decoded codec encoding) :
    ∃ info, frame.value.kind = .dataV1 info ∧ decoded.atoms.length = info.numValues ∧
      start.slots + decoded.atoms.length = decoded.after.slots ∧
      start.rows + decoded.atoms.countP (·.repetition == 0) = decoded.after.rows := by
  obtain ⟨info, _, reps, defs, kind, _, _, _, _, repCount, defCount, values⟩ := wire.original
  obtain ⟨count, _, slots, rows⟩ := slot_counts values (repCount.trans defCount.symm)
  exact ⟨info, kind, count.trans repCount, slots, rows⟩

public theorem v2_page_counts {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {encoding : ValueEncoding}
    (wire : V2PageWire limits plan wrappers source frame start remaining ceiling decoded codec encoding) :
    ∃ info, frame.value.kind = .dataV2 info ∧ decoded.atoms.length = info.numValues ∧
      decoded.atoms.countP (·.repetition == 0) = info.numRows ∧ absentSlots decoded = info.numNulls ∧
      decoded.after.live = 0 ∧ start.slots + decoded.atoms.length = decoded.after.slots ∧
      start.rows + decoded.atoms.countP (·.repetition == 0) = decoded.after.rows := by
  obtain ⟨info, parts, _, checked, kind, _, _, _, levels, _, _, _, headerRows, nulls, _, values, rfl⟩ := wire.original
  obtain ⟨count, pageRows, slots, rows⟩ := slot_counts values (levels.count.trans levels.definitionCount.symm)
  exact ⟨info, kind, count.trans levels.count, pageRows.trans headerRows, nulls, rfl, slots, rows⟩

public theorem data_page_counts {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    (wire : DataPageWire limits plan wrappers source frame start remaining ceiling decoded codec dictionary) :
    start.slots + decoded.atoms.length = decoded.after.slots ∧
      start.rows + decoded.atoms.countP (·.repetition == 0) = decoded.after.rows := by
  cases wire with
  | v1 _ original => obtain ⟨_, _, _, counts⟩ := page_counts original; exact counts
  | v2 _ original => obtain ⟨_, _, _, _, _, _, counts⟩ := v2_page_counts original; exact counts

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk
