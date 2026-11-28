module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.Thms
import Silmaril.Formats.Parquet.Payload.Thms
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.ByteArrayFallback hiding readGroup readFrames FramesWire PageWire
open Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2
open Silmaril.Formats.Arrow.BinaryView Silmaril.Relational

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β}
    {out : β} (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

theorem decodePage_wire {limits : Snappy.Plain.V2.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePage limits metadata source frame = .ok slots) : PageWire limits source frame slots := by
  cases kind : frame.value.kind with
  | dataV1 _ | dictionary _ | skipped _ => simp [decodePage, kind] at read
  | dataV2 header =>
    simp only [decodePage, kind] at read
    split at read
    · rename_i tag
      exact ⟨⟨header, kind, tag⟩, Utf8.Fallback.Snappy.decodePlainBytesWith_wire (mapError_ok read)⟩
    · contradiction

private theorem exact_suffix {frame : Page.Frame} {header : Page.DataV2} {stored decoded : List UInt8}
    (wire : ScalarPage.ExactPayload (frame.value.compressedSize - header.definitionBytes)
      (frame.value.uncompressedSize - header.definitionBytes)
      (ScalarPage.v2Codec Payload.Codec.snappy.id (some header.isCompressed)) stored decoded) :
    stored.length = frame.value.compressedSize - header.definitionBytes ∧
      decoded.length = frame.value.uncompressedSize - header.definitionBytes ∧
      (if header.isCompressed then
        Payload.Decodes (frame.value.uncompressedSize - header.definitionBytes) .snappy stored decoded
       else decoded = stored) := by
  obtain ⟨storedLength, decodedLength, codec, selected, decode⟩ := wire
  refine ⟨storedLength, decodedLength, ?_⟩
  cases flag : header.isCompressed with
  | false =>
    have same : Payload.Codec.uncompressed = codec := by
      apply Option.some.inj
      simpa [ScalarPage.v2Codec, flag, Payload.Codec.ofId_id] using selected
    subst codec
    cases decode
    rfl
  | true =>
    have same : Payload.Codec.snappy = codec := by
      apply Option.some.inj
      simpa [ScalarPage.v2Codec, flag, Payload.Codec.ofId_id] using selected
    subst codec
    exact decode

theorem data_suffix {limits : Snappy.Plain.V2.Limits} {source : Bytes}
    {frame : Page.Frame} {slots : List (Option Bytes)} (wire : PageWire limits source frame slots) :
    Utf8.Dictionary.Snappy.StoredWire limits.file.column.maxPageBytes source frame ∧ SuffixWire limits source frame slots := by
  obtain ⟨⟨header, kind, tag⟩, params, layout, page, original, stored, _, _, prepared, mask, bytes, count⟩ := wire
  simp only [FlatColumn.pageParameters, kind, Option.some.injEq] at original
  subst params
  obtain ⟨nulls, rows, repetition, storedFits, expandedFits, defCap, definitions, encoded, width, split,
    levels, presentCount, payload⟩ := prepared
  obtain ⟨storedSize, expandedSize, suffix⟩ := exact_suffix (header := header) payload
  refine ⟨stored, header, layout, definitions, encoded, kind, tag, repetition, rows, nulls,
    storedFits, expandedFits, defCap, width, split, ?_, ?_, ?_, storedSize, ?_, ?_⟩
  · rwa [mask]
  · rwa [mask]
  · simpa [ByteArrayFallback.declaredSlots, FlatColumn.pageParameters, kind] using count
  · simpa only [bytes] using expandedSize
  · simpa only [bytes] using suffix

private theorem pages_count {limits : Snappy.Plain.V2.Limits} {source : Bytes}
    {frames : List Page.Frame} {pages : List (List (Option Bytes))}
    (ordered : List.Forall₂ (PageWire limits source) frames pages) :
    pages.flatten.length = (frames.map ByteArrayFallback.declaredSlots).sum := by
  induction ordered with
  | nil => rfl
  | cons wire _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, count⟩ := wire
    simp [count, ih]

theorem readFrames_wire {limits : Snappy.Plain.V2.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots := by
  unfold readFrames at read
  obtain ⟨_, checked, read⟩ := bind_ok read
  obtain ⟨fits, exactSize⟩ := Utf8.Dictionary.Snappy.checkExpandedChunk_wire checked
  obtain ⟨dictionary, data, entries, pages, order, dictionaryAt, dataAt, count, opened, ordered, flatten⟩ :=
    ByteArrayFallback.readFramesWith_wire read
  cases dictionary with
  | some frame => cases opened
  | none =>
    have original : frames = data := by simpa using order
    subst data
    have pagesWire := ordered.imp (fun _ _ decoded => decodePage_wire decoded)
    exact ⟨fits, exactSize, dictionaryAt.symm, dataAt, pages, pagesWire, flatten,
      flatten ▸ (pages_count pagesWire).trans count⟩

theorem readGroup_wire {parquet : Snappy.Plain.V2.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, storedCap, decoded⟩ := ByteArrayFallback.readBoundGroupWithCodec_wire read
  have stored := Utf8.Dictionary.Snappy.storedBytes_exact located framed
  refine ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count, codec, located,
    framed, stored, ?_, readFrames_wire decoded⟩
  omega

private theorem denote_successful_prefix {name : String} {limits : Snappy.Plain.V2.Limits}
    {checked : Snappy.Checked name} {before after : List Nat} {groups : List (List (Option Bytes))}
    (earlier : List.Forall₂ (fun index slots => readGroup limits checked index = .ok slots) before groups) :
    let tail := Reader.denoteGroups (rowsAt limits checked) after
    Reader.denoteGroups (rowsAt limits checked) (before ++ after) =
      (groups.map (Plain.ByteArray.File.rows name .optional) ++ tail.1, tail.2) := by
  induction earlier with
  | nil => rfl
  | cons decoded _ ih =>
    simp [Reader.denoteGroups, rowsAt, decoded, Except.map, ih]

theorem readAll_success {name : String} {limits : Snappy.Plain.V2.Limits} {checked : Snappy.Checked name}
    {groups : List (List (Option Bytes))}
    (decoded : List.Forall₂ (fun index slots => readGroup limits checked index = .ok slots)
      (List.range checked.physical.snapshot.groupCount) groups) :
    readAll limits checked = .ok ⟨schema name,
      ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional), .eos⟩⟩ := by
  have ordered := denote_successful_prefix (after := []) decoded
  simp only [List.append_nil, Reader.denoteGroups] at ordered
  rw [readAll, Reader.readAll_opened]
  simp only [source]
  rw [ordered]
  simp only [List.map_map]

theorem readAll_first_error {name : String} {limits : Snappy.Plain.V2.Limits} {checked : Snappy.Checked name}
    {before after : List Nat} {index : Nat} {groups : List (List (Option Bytes))} {cause : Snappy.GroupError}
    (split : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i slots => readGroup limits checked i = .ok slots) before groups)
    (failed : readGroup limits checked index = .error cause) :
    readAll limits checked = .ok ⟨schema name,
      ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional), .readError cause⟩⟩ := by
  rw [readAll, Reader.readAll_opened]
  simp only [source]
  rw [split, denote_successful_prefix (after := index :: after) earlier]
  simp [Reader.denoteGroups, rowsAt, failed, Except.map, List.map_map]

theorem convert_readback {parquet : Snappy.Plain.V2.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {wire : KBytes} (written : convert parquet ipc view input name = .ok wire) :
    ∃ (checked : Snappy.Checked name) (groups : List (List (Option Bytes))) (batches : List (List (Option KBytes))),
      Snappy.openFile parquet input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      readAll parquet checked = .ok ⟨schema name,
        ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional), .eos⟩⟩ ∧
      Stream.read ipc view wire = .ok ⟨⟨name, true, .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) = groups.map (List.map (Option.map Bytes.toList)) ∧
      batches.map List.length = groups.map List.length ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchema ipc wire = .ok (⟨name, true, .binary⟩, start) ∧
        Stream.BatchesWire ipc view wire ⟨name, true, .binary⟩ ipc.batches start batches := by
  obtain ⟨checked, groups, batches, opened, read, decoded, bytes, counts, extent⟩ := Snappy.convertWith_readback written
  have grouped := List.mapM_eq_ok_iff_forall₂.mp read
  exact ⟨checked, groups, batches, opened, grouped.imp (fun _ _ h => readGroup_wire h),
    readAll_success grouped, decoded, bytes, counts, extent⟩

end Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Snappy.Plain.V2
