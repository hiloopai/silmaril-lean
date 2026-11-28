module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Plain.Thms
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

private theorem decodeSlots_wire {plan : Plan} {wrappers : List Nat} {spans : Sections}
    {start : State} {ceiling : Nat} {reps defs : List Nat} {suffix : Bytes} {decoded : Decoded}
    (accepted : decodeSlots plan wrappers spans start ceiling reps defs suffix = .ok decoded) :
    decoded.sections = spans ∧ SlotsWire plan wrappers start ceiling reps defs suffix decoded := by
  unfold decodeSlots at accepted
  obtain ⟨stop, scanned, accepted⟩ := bind_ok accepted
  obtain ⟨words, wordsRead, accepted⟩ := bind_ok accepted
  obtain ⟨aligned, alignedRead, done⟩ := bind_ok accepted
  cases Except.ok.inj done
  have states := scan_wire (from_mapError scanned)
  have alignedWire := FlatPage.reconstruct_ok_iff.mp (from_mapError alignedRead)
  obtain ⟨_, physical, extent, count, widths, values⟩ :=
    Plain.decodeFixedWidth_ok_iff.mp (from_mapError wordsRead)
  exact ⟨rfl, aligned, physical, states, extent, count, widths, alignedWire.1, alignedWire.2.trans values, rfl⟩

public theorem decodePage_wire {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    (accepted : decodePage limits plan wrappers source frame start remaining ceiling = .ok decoded) :
    PageWire limits plan wrappers source frame start remaining ceiling decoded := by
  unfold decodePage at accepted
  obtain ⟨info, header, accepted⟩ := bind_ok accepted
  obtain ⟨status, checked, accepted⟩ := bind_ok accepted
  obtain ⟨reps, repRead, accepted⟩ := bind_ok accepted
  obtain ⟨defs, defRead, slots⟩ := bind_ok accepted
  have crc := from_mapError checked
  obtain ⟨repWire, repCount⟩ := RecursiveSchema.Repeated.Chunk.readLevels_wire (from_mapError repRead)
  obtain ⟨defWire, defCount⟩ := RecursiveSchema.Repeated.Chunk.readLevels_wire (from_mapError defRead)
  have parts := sections_wire (checked_extent crc) repWire defWire
  obtain ⟨layout, ⟨aligned, words, scanned, suffix, count, widths, maskWire, alignedWire, atomsWire⟩⟩ :=
    decodeSlots_wire slots
  exact ⟨info, status, reps, defs, aligned, words,
    RecursiveSchema.Chunk.admitPage_wire (from_mapError header), crc, layout.symm ▸ parts, scanned,
    repCount, defCount, suffix, count, widths, maskWire, alignedWire, atomsWire⟩

private theorem identity_v2 (info : Page.DataV2) :
    RecursiveSchema.Repeated.Chunk.ColumnCodec.uncompressed.v2 info = 0 := by
  cases info with
  | mk _ _ _ _ _ _ flag => cases flag <;> rfl

public theorem decodeV2Page_wire {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    (accepted : decodeV2Page limits plan wrappers source frame start remaining ceiling = .ok decoded) :
    V2PageWire limits plan wrappers source frame start remaining ceiling decoded := by
  unfold decodeV2Page at accepted
  obtain ⟨info, header, accepted⟩ := bind_ok accepted
  obtain ⟨parts, sections, accepted⟩ := bind_ok accepted
  obtain ⟨suffix, suffixRead, accepted⟩ := bind_ok accepted
  obtain ⟨checked, counted, done⟩ := bind_ok accepted
  cases Except.ok.inj done
  obtain ⟨kind, encoding, cap, sizes⟩ := RecursiveSchema.Repeated.Chunk.admitV2Page_wire (from_mapError header)
  have rawLevels := RecursiveSchema.Repeated.Chunk.readV2SectionsWith_wire (from_mapError sections)
  obtain ⟨_, bounded, suffixWire⟩ := RecursiveSchema.Repeated.Chunk.readV2SuffixWith_wire (from_mapError suffixRead)
  cases suffixWire with
  | compressed _ compressed => exact False.elim (compressed (identity_v2 info))
  | raw _ length =>
    change (RecursiveSchema.Repeated.Chunk.bytesAt source parts.spans.values).length =
      frame.value.uncompressedSize - RecursiveSchema.Repeated.Chunk.v2LevelBytes info at length
    have extent : RecursiveSchema.Repeated.Chunk.v2LevelBytes info +
        (RecursiveSchema.Repeated.Chunk.bytesAt source parts.spans.values).length = frame.value.uncompressedSize := by
      omega
    obtain ⟨first, rows, nulls, slots⟩ := RecursiveSchema.Repeated.Chunk.checkV2Counts_wire counted
    obtain ⟨layout, values⟩ := decodeSlots_wire slots
    exact ⟨info, parts, checked, kind, encoding, cap, sizes (identity_v2 info), rawLevels, extent,
      first, rows, nulls, layout, values, rfl⟩

public theorem decodeDataPage_wire {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    (accepted : decodeDataPage limits plan wrappers source frame start remaining ceiling = .ok decoded) :
    DataPageWire limits plan wrappers source frame start remaining ceiling decoded := by
  unfold decodeDataPage at accepted
  split at accepted
  · exact .v2 (decodeV2Page_wire accepted)
  · exact .v1 (decodePage_wire accepted)

private theorem slot_counts {plan : Plan} {wrappers : List Nat} {start : State} {ceiling : Nat}
    {reps defs : List Nat} {suffix : Bytes} {decoded : Decoded}
    (wire : SlotsWire plan wrappers start ceiling reps defs suffix decoded)
    (balanced : reps.length = defs.length) :
    decoded.atoms.length = reps.length ∧ decoded.atoms.countP (·.repetition == 0) = reps.count 0 ∧
      start.slots + decoded.atoms.length = decoded.after.slots ∧
      start.rows + decoded.atoms.countP (·.repetition == 0) = decoded.after.rows := by
  obtain ⟨aligned, _, scanned, _, _, _, maskWire, _, atomsWire⟩ := wire.original
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
    (wire : PageWire limits plan wrappers source frame start remaining ceiling decoded) :
    ∃ info, frame.value.kind = .dataV1 info ∧ decoded.atoms.length = info.numValues ∧
      start.slots + decoded.atoms.length = decoded.after.slots ∧
      start.rows + decoded.atoms.countP (·.repetition == 0) = decoded.after.rows := by
  obtain ⟨info, _, reps, defs, aligned, words, header, _, _, scanned, repCount, defCount,
    suffix, count, widths, maskWire, alignedWire, atomsWire⟩ := wire.original
  have slotsWire : SlotsWire plan wrappers start ceiling reps.levels defs.levels defs.tail decoded :=
    ⟨aligned, words, scanned, suffix, count, widths, maskWire, alignedWire, atomsWire⟩
  obtain ⟨count, _, slots, rows⟩ := slot_counts slotsWire (repCount.trans defCount.symm)
  exact ⟨info, header.kind, count.trans repCount, slots, rows⟩

public theorem v2_page_counts {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    (wire : V2PageWire limits plan wrappers source frame start remaining ceiling decoded) :
    ∃ info, frame.value.kind = .dataV2 info ∧ decoded.atoms.length = info.numValues ∧
      decoded.atoms.countP (·.repetition == 0) = info.numRows ∧ absentSlots decoded = info.numNulls ∧
      decoded.after.live = 0 ∧ start.slots + decoded.atoms.length = decoded.after.slots ∧
      start.rows + decoded.atoms.countP (·.repetition == 0) = decoded.after.rows := by
  obtain ⟨info, parts, checked, kind, _, _, _, levels, _, _, headerRows, nulls, _, values, rfl⟩ := wire.original
  obtain ⟨count, pageRows, slots, rows⟩ := slot_counts values (levels.count.trans levels.definitionCount.symm)
  exact ⟨info, kind, count.trans levels.count, pageRows.trans headerRows, nulls, rfl, slots, rows⟩

public theorem data_page_counts {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    (wire : DataPageWire limits plan wrappers source frame start remaining ceiling decoded) :
    start.slots + decoded.atoms.length = decoded.after.slots ∧
      start.rows + decoded.atoms.countP (·.repetition == 0) = decoded.after.rows := by
  cases wire with
  | v1 original => obtain ⟨_, _, _, counts⟩ := page_counts original; exact counts
  | v2 original => obtain ⟨_, _, _, _, _, _, counts⟩ := v2_page_counts original; exact counts

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk
