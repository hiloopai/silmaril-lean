module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Cursor
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Plain.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk

open Silmaril.Formats (Bytes)
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (read : (first >>= next) = .ok value) : ∃ found, first = .ok found ∧ next found = .ok value := by
  cases first with
  | error => contradiction
  | ok result => exact ⟨result, rfl, read⟩

private theorem from_mapError {α ε δ : Type} {first : Except ε α} {wrap : ε → δ} {value : α}
    (read : first.mapError wrap = .ok value) : first = .ok value := by
  cases first with
  | error => simp [Except.mapError] at read
  | ok => simpa only [Except.mapError, Except.ok.injEq] using read

private theorem decodeSlots_wire {plan : Plan} {ceiling : Nat} {start : State}
    {reps defs : List Nat} {suffix : Bytes} {decoded : Decoded}
    (accepted : decodeSlots plan ceiling start reps defs suffix = .ok decoded) :
    DecodedWire plan ceiling start reps defs suffix decoded := by
  unfold decodeSlots at accepted
  obtain ⟨classified, levelRead, read⟩ := bind_ok accepted
  obtain ⟨values, valueRead, read⟩ := bind_ok read
  obtain ⟨aligned, alignment, packaged⟩ := bind_ok read
  obtain ⟨_, words, exactWords, wordCount, width, ordered⟩ :=
    Plain.decodeFixedWidth_ok_iff.mp (from_mapError valueRead)
  obtain ⟨mask, positions⟩ := FlatPage.reconstruct_ok_iff.mp (from_mapError alignment)
  cases Except.ok.inj packaged
  exact ⟨classify_wire (from_mapError levelRead), words, exactWords, wordCount, width, mask,
    positions.trans ordered⟩

private theorem checksum_extent {cap : Nat} {source : Bytes} {frame : Page.Frame}
    {checksum : Page.Checksum.Status} (checked : Page.Checksum.verify cap source frame = .ok checksum) :
    Page.Checksum.PayloadWithin source frame := by
  cases checksum with
  | absent => exact (Page.Checksum.verify_absent_iff.mp checked).2.1
  | valid crc => exact (Page.Checksum.verify_valid_iff.mp checked).2.1

public theorem decodePage_wire {limits : Limits} {plan : Plan} {source : Bytes}
    {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    (accepted : decodePage limits plan source frame start remaining ceiling = .ok decoded) :
    PageWire limits plan source frame start remaining ceiling decoded := by
  unfold decodePage at accepted
  obtain ⟨info, header, read⟩ := bind_ok accepted
  obtain ⟨checksum, checksumRead, read⟩ := bind_ok read
  obtain ⟨reps, repRead, read⟩ := bind_ok read
  obtain ⟨defs, defRead, read⟩ := bind_ok read
  have checked := from_mapError checksumRead
  obtain ⟨bodySlice, bodySize⟩ := Page.Checksum.payload_exact (checksum_extent checked)
  obtain ⟨repetition, repCount⟩ :=
    RecursiveSchema.Repeated.Chunk.readLevels_wire (from_mapError repRead)
  obtain ⟨definition, _⟩ :=
    RecursiveSchema.Repeated.Chunk.readLevels_wire (from_mapError defRead)
  have slots := decodeSlots_wire read
  have count : decoded.levels.length = info.numValues := by
    simpa only [List.length_map, repCount] using congrArg List.length (original_levels slots.levels).1
  exact ⟨info, _, checksum, reps, defs, RecursiveSchema.Chunk.admitPage_wire (from_mapError header),
    checked, bodySlice, bodySize, repetition, definition, slots, count⟩

public theorem page_counts {limits : Limits} {plan : Plan} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    (wire : PageWire limits plan source frame start remaining ceiling decoded) :
    start.slots + decoded.levels.length = decoded.after.slots ∧
    start.rows + decoded.levels.countP Slot.startsRow = decoded.after.rows := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, slots, _⟩ := wire.original
  exact slot_counts slots.levels

private theorem decodeFrames_wire {limits : Limits} {carrier : Carrier} {frames : List Page.Frame}
    {ordinal : Nat} {state : State} {reversed : List ObservedPage} {out : Observation}
    (accepted : decodeFrames limits carrier frames ordinal state reversed = .ok out) :
    ∃ pages, out.pages = reversed.reverse ++ pages ∧ ChainWire limits carrier state frames pages out.stop := by
  induction frames generalizing ordinal state reversed out with
  | nil =>
    cases Except.ok.inj accepted
    exact ⟨[], by simp, .nil state⟩
  | cons frame frames ih =>
    simp only [decodeFrames] at accepted
    obtain ⟨decoded, first, rest⟩ := bind_ok accepted
    obtain ⟨pages, eq, wire⟩ := ih rest
    refine ⟨⟨frame, state, decoded⟩ :: pages, ?_, .cons (decodePage_wire (from_mapError first)) wire⟩
    simpa [List.reverse_cons, List.append_assoc] using eq

private theorem chain_frames {limits : Limits} {carrier : Carrier} {start stop : State}
    {frames : List Page.Frame} {pages : List ObservedPage}
    (wire : ChainWire limits carrier start frames pages stop) :
    pages.map ObservedPage.frame = frames := by
  induction wire <;> simp_all

public theorem chain_counts {limits : Limits} {carrier : Carrier} {start stop : State}
    {frames : List Page.Frame} {pages : List ObservedPage}
    (wire : ChainWire limits carrier start frames pages stop) :
    start.slots + (pages.flatMap (·.decoded.levels)).length = stop.slots ∧
      start.rows + (pages.flatMap (·.decoded.levels)).countP Slot.startsRow = stop.rows := by
  induction wire with
  | nil => simp
  | cons first _ ih =>
    obtain ⟨slots, rows⟩ := page_counts first
    obtain ⟨tailSlots, tailRows⟩ := ih
    simp only [List.flatMap_cons, List.length_append, List.countP_append]
    omega

public theorem read_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Limits}
    {binding : Binding schema group} {out : Observation}
    (accepted : RecursiveSchema.TwoList.Chunk.read limits binding = .ok out) : Wire limits (carrierOf binding) out := by
  unfold RecursiveSchema.TwoList.Chunk.read at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  · rename_i chunkCap
    split at accepted
    · contradiction
    · rename_i slotCap
      split at accepted
      · contradiction
      · rename_i rowCap
        split at accepted
        · contradiction
        · rename_i raw
          obtain ⟨frames, scan, accepted⟩ := bind_ok accepted
          obtain ⟨decoded, bodyRead, accepted⟩ := bind_ok accepted
          split at accepted
          · contradiction
          · rename_i slots
            split at accepted
            · contradiction
            · rename_i rows
              cases Except.ok.inj accepted
              obtain ⟨_, eq, wire⟩ := decodeFrames_wire bodyRead
              simp only [List.reverse_nil, List.nil_append] at eq
              rw [← eq] at wire
              have framesEq := chain_frames wire
              have scanExact := framesEq.symm ▸ from_mapError scan
              exact ⟨scanExact, (Page.readChunk_chain scanExact).2.2, framesEq.symm ▸ wire,
                Decidable.not_not.mp raw, Decidable.not_not.mp slots, Decidable.not_not.mp rows,
                Nat.le_of_not_gt chunkCap, Nat.le_of_not_gt slotCap, Nat.le_of_not_gt rowCap⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk
