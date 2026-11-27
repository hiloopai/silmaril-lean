module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Delta.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.DeltaBinaryPacked.Thms
import Silmaril.Formats.Parquet.DeltaPage.Thms
import Silmaril.Formats.Parquet.Timestamp.Page.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Footer.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Delta

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Numeric.Timestamp (Ticks)
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Delta

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
    Leaf.selectChunkWith .deltaBinaryPacked limits bound index = .ok group.chunk ∧
      bound.snapshot.groupAt index = some group.chunk.group ∧
      group.chunk.group.columns[bound.ordinal - 1]? = some group.chunk.column ∧
      (group.chunk.column.metadata.codec = 0 ∨ group.chunk.column.metadata.codec = 1) ∧
      group.chunk.column.metadata.dictionaryPageOffset = none ∧
      (group.chunk.span.start : Int) = group.chunk.column.metadata.dataPageOffset ∧
      (group.chunk.span.stop : Int) =
        group.chunk.column.metadata.dataPageOffset + group.chunk.column.metadata.totalCompressedSize ∧
      Parquet.Page.readChunk limits.framing bound.snapshot.bytes group.chunk.span = .ok group.frames ∧
      Parquet.Page.Chain group.chunk.span group.chunk.span.start group.chunk.span.stop group.frames ∧
      (group.frames.map Leaf.Internal.pageSlots).sum = group.chunk.group.numRows.toNat := by
  unfold checkGroup at checked
  obtain ⟨chunk, selected, checked⟩ := bind_ok checked
  obtain ⟨frames, parsed, checked⟩ := bind_ok checked
  have wire := mapError_ok parsed
  by_cases rows : (frames.map Leaf.Internal.pageSlots).sum = chunk.group.numRows.toNat
  · simp [rows, pure, Except.pure] at checked
    subst group
    obtain ⟨original, column, _, _, _, codec, metadata, _, span, _⟩ := Leaf.selectChunkWith_sound selected
    have noDict := Leaf.ChunkEncoding.deltaBinaryPacked_noDictionary metadata
    have offset := Footer.checkDataSpan_some_iff.mp (by
      simpa [Parquet.Page.columnSpan, noDict] using span)
    exact ⟨selected, original, column, by simpa [Leaf.ChunkEncoding.admitsCodec] using codec,
      noDict, offset.1, offset.2.1, wire, (Parquet.Page.readChunk_chain wire).2.2, rows⟩
  · simp [rows, Bind.bind, Except.bind] at checked

private theorem params_count {bound : Bound} {frame : Parquet.Page.Frame} {codec : Int}
    {params : ScalarPage.Parameters}
    (checked : Timestamp.Page.parameters bound.binding.leaf bound.levels codec frame.value = .ok params) :
    params.numValues = Leaf.Internal.pageSlots frame := by
  have wire := (Timestamp.Page.parameters_sound checked).2.2.2.2
  cases kind : frame.value.kind <;> simp [Leaf.Internal.pageSlots, kind] at wire ⊢
  all_goals exact wire.1

theorem decodePage_wire {packed : DeltaBinaryPacked.Limits} {limits : ScalarPage.Limits}
    {bound : Bound} {codec : Int} {frame : Parquet.Page.Frame} {ordinal : Nat}
    {slots : List (Option Int64)} (read : decodePage packed limits bound codec frame ordinal = .ok slots) :
    PageWire packed limits bound codec frame slots := by
  unfold decodePage at read
  obtain ⟨status, verified, read⟩ := bind_ok read
  obtain ⟨params, admitted, read⟩ := bind_ok read
  have parsed := mapError_ok admitted
  have decoded := mapError_ok read
  obtain ⟨slice, size, cap, crc⟩ := Leaf.Dictionary.Snappy.stored_verified (mapError_ok verified)
  obtain ⟨encoding, layout, prepared, words, tag, validation, preparation, values, mask, present⟩ :=
    DeltaPage.decode_wire_sound decoded
  cases encoding with
  | binaryPacked =>
    change (DeltaBinaryPacked.decode .int64 packed (prepared.mask.count true) prepared.scalars).mapError
      DeltaPage.Error.binaryPacked = .ok words at values
    obtain ⟨stream, byteBound, bytes, valid, reconstructed, count⟩ :=
      DeltaBinaryPacked.decode_sound (mapError_ok values)
    have rows := (DeltaPage.decode_counts decoded).1.trans (params_count parsed)
    exact ⟨status, params, layout, prepared, stream, mapError_ok verified, slice, size, cap, by cases status <;> exact crc, parsed,
      tag, validation, preparation, byteBound, bytes, valid, mask, present.trans reconstructed, rows,
      present ▸ count⟩

theorem pageWire_extents {packed : DeltaBinaryPacked.Limits} {limits : ScalarPage.Limits}
    {bound : Bound} {codec : Int} {frame : Parquet.Page.Frame} {slots : List (Option Int64)}
    (wire : PageWire packed limits bound codec frame slots) :
    let stored := Leaf.Internal.body bound frame
    ∃ (prepared : ScalarPage.Prepared) (stream : DeltaBinaryPacked.Stream),
      prepared.scalars.toList = stream.wire ∧ slots.filterMap id = stream.reconstruct .int64 ∧
      match frame.value.kind with
      | .dataV1 header =>
        header.encoding = 5 ∧ ∃ expanded layout sections,
          ScalarPage.ExactPayload frame.value.compressedSize frame.value.uncompressedSize
            codec stored.toList expanded ∧
          FlatPage.split layout limits.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
          FlatPage.readMask layout header.numValues limits.levels sections.definitions = .ok prepared.mask ∧
          sections.scalars = prepared.scalars
      | .dataV2 header =>
        header.encoding = 5 ∧ header.repetitionBytes = 0 ∧ header.numRows = header.numValues ∧
        header.definitionBytes ≤ frame.value.compressedSize ∧ header.definitionBytes ≤ frame.value.uncompressedSize ∧
        ∃ (definitions : Bytes) (suffix : List UInt8) (layout : FlatPage.Layout),
          definitions.length = header.definitionBytes ∧ stored.toList = definitions.toList ++ suffix ∧
          FlatPage.readMask layout header.numValues limits.levels definitions = .ok prepared.mask ∧
          (slots.filterMap id).length = header.numValues - header.numNulls ∧
          ScalarPage.ExactPayload (frame.value.compressedSize - header.definitionBytes)
            (frame.value.uncompressedSize - header.definitionBytes)
            (ScalarPage.v2Codec codec (some header.isCompressed)) suffix prepared.scalars.toList
      | _ => False := by
  obtain ⟨_, params, layout, prepared, stream, _, _, _, _, _, selected, tag, _, physical,
    _, bytes, _, _, values, _, present⟩ := wire
  obtain ⟨_, _, codecEq, sizes, header⟩ := Timestamp.Page.parameters_sound selected
  refine ⟨prepared, stream, bytes, values, ?_⟩
  cases kind : frame.value.kind with
  | dataV1 info =>
    simp only [kind] at header
    obtain ⟨count, encoding, version⟩ := header
    rw [ScalarPage.PreparedWire, version, sizes, codecEq, count] at physical
    obtain ⟨_, _, expanded, slices, extent, split, mask, scalars⟩ := physical
    exact ⟨encoding.symm.trans tag, expanded, layout, slices, extent, split, mask, scalars.symm⟩
  | dataV2 info =>
    simp only [kind] at header
    obtain ⟨count, encoding, version⟩ := header
    rw [ScalarPage.PreparedWire, version, sizes, codecEq, count] at physical
    obtain ⟨_, rows, repetition, storedFits, expandedFits, _, definitions, suffix, definitionSize,
      split, mask, presentCount, extent⟩ := physical
    exact ⟨encoding.symm.trans tag, repetition, rows, storedFits, expandedFits, definitions, suffix,
      layout, definitionSize, split, mask, present.trans presentCount, extent⟩
  | dictionary _ | skipped _ => simp only [kind] at header

private theorem fold_signed (deltas : List Int) (first : Int64) :
    (deltas.foldl (DeltaBinaryPacked.Physical.step .int64) first).toInt =
      deltas.foldl (fun previous delta => (previous + delta).bmod (2^64)) first.toInt := by
  induction deltas generalizing first with
  | nil => rfl
  | cons delta rest ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    exact congrArg (rest.foldl (fun previous delta => (previous + delta).bmod (2^64)))
      (DeltaBinaryPacked.step_toInt .int64 first delta)

theorem reconstruct_signed (stream : DeltaBinaryPacked.Stream) (index : Nat)
    (bounded : index < (stream.reconstruct .int64).length) :
    ((stream.reconstruct .int64)[index]).toInt =
      (stream.deltas.take index).foldl (fun previous delta => (previous + delta).bmod (2^64))
        (Int64.ofInt stream.header.first).toInt := by
  rw [DeltaBinaryPacked.reconstruct_getElem bounded]
  exact fold_signed _ _

theorem readGroup_wire {packed : DeltaBinaryPacked.Limits} {limits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readGroup packed limits bound index = .ok slots) :
    ∃ group pages, checkGroup limits bound index = .ok group ∧
      List.Forall₂ (PageWire packed limits.page bound group.chunk.column.metadata.codec) group.frames pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = group.chunk.group.numRows.toNat := by
  unfold readGroup at read
  obtain ⟨group, checked, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  have raw : List.Forall₂ (PageWire packed limits.page bound group.chunk.column.metadata.codec) group.frames pages := by
    rw [← List.zipIdx_map_fst 0 group.frames, List.forall₂_map_left_iff]
    exact (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun _ _ read => decodePage_wire read
  have counts : pages.map List.length = group.frames.map Leaf.Internal.pageSlots := by
    clear read checked decoded
    generalize group.frames = frames at raw ⊢
    induction raw with
    | nil => rfl
    | cons head _ ih =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, count, _⟩ := head
      exact congrArg₂ List.cons count ih
  have mapped := (Except.ok.inj read).symm
  refine ⟨group, pages, checked, raw, mapped, ?_, ?_⟩
  · rw [mapped, List.map_map]
    apply List.map_congr_left
    intro slot _
    cases slot <;> rfl
  · obtain ⟨_, _, _, _, _, _, _, _, _, rows⟩ := checkGroup_wire checked
    rw [mapped, List.length_map, List.length_flatten, counts, rows]

theorem readGroup_first_page_error {packed : DeltaBinaryPacked.Limits} {limits : Leaf.Limits} {bound : Bound} {index ordinal : Nat}
    {group : CheckedGroup} {frame : Parquet.Page.Frame} {before after : List (Parquet.Page.Frame × Nat)}
    {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (checked : checkGroup limits bound index = .ok group)
    (split : group.frames.zipIdx = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => decodePage packed limits.page bound group.chunk.column.metadata.codec item i) = .ok outputs)
    (failed : decodePage packed limits.page bound group.chunk.column.metadata.codec frame ordinal = .error cause) :
    readGroup packed limits bound index = .error cause := by
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

theorem convert_readback {packed : DeltaBinaryPacked.Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert packed inputLimits outputLimits input ordinal = .ok wire) :
    ∃ bound : Bound, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound ∧
      ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = Leaf.Events.ToIpc.selectedBinding bound ∧
        List.Forall₂ (fun index counts =>
          ∃ slots, readGroup packed inputLimits.leaf bound index = .ok slots ∧
            counts = slots.map (Option.map Ticks.ticks))
          (List.range bound.snapshot.groupCount)
          (result.batches.map Arrow.TimestampBatch.Writer.tickCounts) := by
  obtain ⟨bound, opened, ended, result, readback, metadata, exactTicks⟩ :=
    Leaf.Events.ToIpc.convertGroups_readback written
  exact ⟨bound, opened, result, readback, metadata, exactTicks ▸ reference_complete ended⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Delta
