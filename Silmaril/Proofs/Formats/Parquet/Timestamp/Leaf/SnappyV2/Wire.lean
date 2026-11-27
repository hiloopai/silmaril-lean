module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.SnappyV2

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Numeric.Timestamp (Ticks)
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots selectChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

theorem checkGroup_wire {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {group : CheckedGroup} (checked : checkGroup limits bound index = .ok group) :
    selectChunk {limits with allowSnappy := true} bound index = .ok group.chunk ∧
      group.chunk.column.metadata.codec = Payload.Codec.snappy.id ∧
      Parquet.Page.readChunk limits.framing bound.snapshot.bytes group.chunk.span = .ok group.frames ∧
      Parquet.Page.Chain group.chunk.span group.chunk.span.start group.chunk.span.stop group.frames ∧
      (group.frames.map Leaf.Internal.pageSlots).sum = group.chunk.group.numRows.toNat := by
  unfold checkGroup at checked
  obtain ⟨chunk, selected, checked⟩ := bind_ok checked
  by_cases codec : chunk.column.metadata.codec = Payload.Codec.snappy.id
  · simp only [codec, ne_eq, not_true_eq_false, ↓reduceIte] at checked
    obtain ⟨frames, framed, checked⟩ := bind_ok checked
    have wire := mapError_ok framed
    by_cases rows : (frames.map Leaf.Internal.pageSlots).sum = chunk.group.numRows.toNat
    · simp only [rows, not_true_eq_false, ↓reduceIte] at checked
      cases Except.ok.inj checked
      exact ⟨selected, codec, wire, (Parquet.Page.readChunk_chain wire).2.2, rows⟩
    · simp [rows, Bind.bind, Except.bind] at checked
  · simp [codec, Bind.bind, Except.bind] at checked

private theorem params_v2 {bound : Bound} {frame : Parquet.Page.Frame} {info : Parquet.Page.DataV2}
    {params : ScalarPage.Parameters} (v2 : frame.value.kind = .dataV2 info)
    (checked : Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.snappy.id frame.value =
      .ok params) :
    params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
      info.numValues, Payload.Codec.snappy.id, info.encoding,
      .v2 info.numNulls info.numRows info.repetitionBytes info.definitionBytes
        (some info.isCompressed)⟩ := by
  unfold Timestamp.Page.parameters at checked
  split at checked
  · simp only [v2, Except.ok.injEq] at checked
    cases checked
    rfl
  · contradiction

theorem decodePage_wire {limits : ScalarPage.Limits} {bound : Bound} {frame : Parquet.Page.Frame}
    {ordinal : Nat} {slots : List (Option Int64)} (read : decodePage limits bound frame ordinal = .ok slots) :
    PageWire limits bound frame slots := by
  unfold decodePage at read
  cases header : frame.value.kind with
  | dataV2 info =>
    simp only [header] at read
    obtain ⟨status, verified, read⟩ := bind_ok read
    obtain ⟨params, admitted, read⟩ := bind_ok read
    have parsed := mapError_ok admitted
    have decoded := mapError_ok read
    have counts := (ScalarPage.decode_counts decoded).1
    rw [params_v2 header parsed] at counts
    exact ⟨info, status, params, header, mapError_ok verified, parsed, decoded, counts⟩
  | dataV1 _ | dictionary _ | skipped _ => simp [header] at read

theorem pageWire_prepared {limits : ScalarPage.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {slots : List (Option Int64)} (wire : PageWire limits bound frame slots) :
    let stored := Leaf.Internal.body bound frame
    ∃ info status params layout prepared words,
      frame.value.kind = .dataV2 info ∧
      params = ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩, bound.levels,
        info.numValues, Payload.Codec.snappy.id, info.encoding,
        .v2 info.numNulls info.numRows info.repetitionBytes info.definitionBytes
          (some info.isCompressed)⟩ ∧
      bound.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.compressedBytes ∧
      (match status with
       | Parquet.Page.Checksum.Status.absent => frame.value.crc = none
       | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
      params.sizes.uncompressed ≤ limits.uncompressedBytes ∧
      ScalarPage.validate params limits stored = .ok layout ∧
      ScalarPage.PreparedWire params limits layout stored prepared ∧
      Plain.decodeInt64 (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words := by
  obtain ⟨info, status, params, v2, verified, header, decoded, _⟩ := wire
  obtain ⟨slice, size, cap, crc⟩ := Leaf.Dictionary.Snappy.stored_verified verified
  obtain ⟨prepared, words, read, raw, mask, values, _, _⟩ := ScalarPage.decode_sound decoded
  obtain ⟨layout, admitted, exactBytes⟩ := ScalarPage.prepare_sound read
  have sizes := Leaf.Dictionary.Snappy.expanded_bound admitted
  cases status with
  | absent =>
    exact ⟨info, .absent, params, layout, prepared, words, v2, params_v2 v2 header,
      slice, size, cap, crc, sizes, admitted, exactBytes, raw, mask, values⟩
  | valid checksum =>
    exact ⟨info, .valid checksum, params, layout, prepared, words, v2, params_v2 v2 header,
      slice, size, cap, crc, sizes, admitted, exactBytes, raw, mask, values⟩

theorem readGroup_wire {limits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readGroup limits bound index = .ok slots) :
    ∃ group pages, checkGroup limits bound index = .ok group ∧
      List.Forall₂ (PageWire limits.page bound) group.frames pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = group.chunk.group.numRows.toNat := by
  unfold readGroup at read
  obtain ⟨group, checked, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  have raw : List.Forall₂ (PageWire limits.page bound) group.frames pages := by
    rw [← List.zipIdx_map_fst 0 group.frames, List.forall₂_map_left_iff]
    exact (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun _ _ read => decodePage_wire read
  have counts : pages.map List.length = group.frames.map Leaf.Internal.pageSlots := by
    clear read checked decoded
    generalize group.frames = frames at raw ⊢
    induction raw with
    | nil => rfl
    | cons head _ ih =>
      obtain ⟨info, _, _, version, _, _, _, count⟩ := head
      exact congrArg₂ List.cons (by simpa [Leaf.Internal.pageSlots, version] using count) ih
  have mapped := (Except.ok.inj read).symm
  refine ⟨group, pages, checked, raw, mapped, ?_, ?_⟩
  · rw [mapped, List.map_map]
    apply List.map_congr_left
    intro slot _
    cases slot <;> rfl
  · rw [mapped, List.length_map, List.length_flatten, counts, (checkGroup_wire checked).2.2.2.2]

theorem readGroup_first_page_error {limits : Leaf.Limits} {bound : Bound} {index ordinal : Nat}
    {group : CheckedGroup} {frame : Parquet.Page.Frame} {before after : List (Parquet.Page.Frame × Nat)}
    {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (checked : checkGroup limits bound index = .ok group)
    (split : group.frames.zipIdx = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => decodePage limits.page bound item i) = .ok outputs)
    (failed : decodePage limits.page bound frame ordinal = .error cause) :
    readGroup limits bound index = .error cause := by
  simp [readGroup, checked, split, earlier, failed, Bind.bind, Except.bind]

private theorem reference_complete {bound : Bound} {read : Nat → Except Leaf.Error (Slots bound)}
    {indices : List Nat} (ended : (Leaf.Events.referenceGroupsWith read indices).2 = .eos) :
    List.Forall₂ (fun index counts =>
      ∃ slots, read index = .ok slots ∧ counts = slots.map (Option.map Ticks.ticks))
      indices ((Leaf.Events.referenceGroupsWith read indices).1.map (List.map (Option.map Ticks.ticks))) := by
  induction indices with
  | nil => exact .nil
  | cons index rest ih =>
    cases decoded : read index with
    | error cause => simp [Leaf.Events.referenceGroupsWith, decoded] at ended
    | ok slots =>
      simp only [Leaf.Events.referenceGroupsWith, decoded, List.map_cons] at ended ⊢
      exact .cons ⟨slots, decoded, rfl⟩ (ih ended)

theorem convert_readback {inputLimits : Leaf.Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert inputLimits outputLimits input ordinal = .ok wire) :
    ∃ bound : Bound, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound ∧
      ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = Leaf.Events.ToIpc.selectedBinding bound ∧
        List.Forall₂ (fun index counts =>
          ∃ slots, readGroup inputLimits.leaf bound index = .ok slots ∧
            counts = slots.map (Option.map Ticks.ticks))
          (List.range bound.snapshot.groupCount)
          (result.batches.map Arrow.TimestampBatch.Writer.tickCounts) := by
  obtain ⟨bound, opened, ended, result, readback, metadata, exactTicks⟩ :=
    Leaf.Events.ToIpc.convertGroups_readback written
  exact ⟨bound, opened, result, readback, metadata, exactTicks ▸ reference_complete ended⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.SnappyV2
