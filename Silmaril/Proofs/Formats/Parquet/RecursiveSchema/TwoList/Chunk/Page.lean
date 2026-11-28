module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Cursor
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Plain.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk

open Silmaril.Formats (Bytes)
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk

public theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (read : (first >>= next) = .ok value) : ∃ found, first = .ok found ∧ next found = .ok value := by
  cases first with
  | error => contradiction
  | ok result => exact ⟨result, rfl, read⟩

public theorem from_mapError {α ε δ : Type} {first : Except ε α} {wrap : ε → δ} {value : α}
    (read : first.mapError wrap = .ok value) : first = .ok value := by
  cases first with
  | error => simp [Except.mapError] at read
  | ok => simpa only [Except.mapError, Except.ok.injEq] using read

public theorem decodeSlots_wire {plan : Plan} {ceiling : Nat} {start : State}
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

public theorem decodePage_wire {limits : Limits} {plan : Plan} {source : Bytes}
    {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded} {codec : Codec}
    (accepted : decodePage limits plan source frame start remaining ceiling codec = .ok decoded) :
    PageWire limits plan source frame start remaining ceiling decoded codec := by
  unfold decodePage at accepted
  obtain ⟨info, header, read⟩ := bind_ok accepted
  obtain ⟨body, bodyRead, read⟩ := bind_ok read
  obtain ⟨reps, repRead, read⟩ := bind_ok read
  obtain ⟨defs, defRead, read⟩ := bind_ok read
  have admitted := from_mapError header
  unfold RecursiveSchema.Repeated.Chunk.admitPage at admitted
  obtain ⟨kind, encodings, cap, sizes⟩ := RecursiveSchema.Chunk.admitPageWith_wire (from_mapError admitted)
  have bodyWire := RecursiveSchema.Repeated.Chunk.readV1Body_wire sizes (from_mapError bodyRead)
  obtain ⟨repetition, repCount⟩ :=
    RecursiveSchema.Repeated.Chunk.readLevels_wire (from_mapError repRead)
  obtain ⟨definition, _⟩ :=
    RecursiveSchema.Repeated.Chunk.readLevels_wire (from_mapError defRead)
  have slots := decodeSlots_wire read
  have count : decoded.levels.length = info.numValues := by
    simpa only [List.length_map, repCount] using congrArg List.length (original_levels slots.levels).1
  exact ⟨info, body, reps, defs, kind, encodings, cap, bodyWire, repetition, definition, slots, count⟩

public theorem v1_counts {limits : Limits} {plan : Plan} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining ceiling : Nat} {decoded : Decoded} {codec : Codec}
    (wire : PageWire limits plan source frame start remaining ceiling decoded codec) :
    start.slots + decoded.levels.length = decoded.after.slots ∧
    start.rows + decoded.levels.countP Slot.startsRow = decoded.after.rows := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, slots, _⟩ := wire.original
  exact slot_counts slots.levels

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk
