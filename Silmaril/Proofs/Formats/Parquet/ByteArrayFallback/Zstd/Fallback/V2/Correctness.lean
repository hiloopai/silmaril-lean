module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Thms
import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Thms
import Silmaril.Formats.Arrow.BinaryView.Stream.Thms
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.ByteArrayFallback hiding readDictionary readGroup readFrames FramesWire PageWire
open Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2
open Silmaril.Formats.Arrow.BinaryView

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

open Silmaril.Relational Silmaril.Formats.Arrow

theorem decodePage_wire {limits : Zstd.Fallback.V2.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {dictionary : Option (Array Bytes)} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePage limits metadata source dictionary frame = .ok slots) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame slots := by
  cases dictionary with
  | none => contradiction
  | some entries =>
    cases kind : frame.value.kind with
    | dataV1 _ | dictionary _ | skipped _ => simp [decodePage, kind] at read
    | dataV2 header =>
      simp only [decodePage, kind] at read
      split at read
      · exact ⟨entries, rfl, .inr (Zstd.Plain.V2.decodePage_wire (mapError_ok read))⟩
      · obtain ⟨_, same, wire⟩ := Zstd.Dictionary.V2.decodePage_wire (mapError_ok read)
        cases same
        exact ⟨entries, rfl, .inl wire⟩

theorem data_checksum {limits : Zstd.Fallback.V2.Limits} {source : Bytes} {entries : Array Bytes}
    {frame : Page.Frame} {slots : List (Option Bytes)} (wire : PageWire limits source entries frame slots) :
    Utf8.Dictionary.Snappy.StoredWire limits.file.column.maxPageBytes source frame := by
  rcases wire with dictionary | plain
  · exact dictionary.1
  · exact plain.1

private theorem pages_count {limits : Zstd.Fallback.V2.Limits} {source : Bytes}
    {entries : Array Bytes} {frames : List Page.Frame} {pages : List (List (Option Bytes))}
    (ordered : List.Forall₂ (PageWire limits source entries) frames pages) :
    pages.flatten.length = (frames.map ByteArrayFallback.declaredSlots).sum := by
  induction ordered with
  | nil => rfl
  | cons wire _ ih =>
    rcases wire with dictionary | plain
    · obtain ⟨_, _, data, _, _, _, _, _, kind, _, _, _, _, _, _, _, _, _, _, _, count, _⟩ := dictionary
      simp [count, ih, ByteArrayFallback.declaredSlots, FlatColumn.pageParameters, kind]
    · obtain ⟨_, _, data, _, _, _, kind, _, _, _, _, _, _, _, _, _, _, _, count, _⟩ := plain
      simp [count, ih, ByteArrayFallback.declaredSlots, FlatColumn.pageParameters, kind]

theorem readFrames_wire {limits : Zstd.Fallback.V2.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots := by
  unfold ByteArrayFallback.Zstd.Fallback.V2.readFrames at read
  obtain ⟨_, checked, read⟩ := bind_ok read
  have ⟨fits, size⟩ := Utf8.Dictionary.Snappy.checkExpandedChunk_wire checked
  refine ⟨fits, size, ?_⟩
  cases split : ByteArrayFallback.splitLeading frames with
  | mk leading originalData =>
    simp only [split] at read
    obtain ⟨_, phaseCheck, read⟩ := bind_ok read
    have schedule := Utf8.Fallback.checkPhasesWith_wire phaseCheck
    obtain ⟨dictionary, data, entries, pages, order, dictionaryAt, dataAt, count, opened, ordered, flatten⟩ :=
      ByteArrayFallback.readFramesWith_wire read
    cases dictionary with
    | none =>
      cases opened
      cases data with
      | nil => simp at dataAt
      | cons frame rest =>
        cases ordered with
        | cons first _ =>
          obtain ⟨_, impossible, _⟩ := decodePage_wire first
          contradiction
    | some frame =>
      obtain ⟨raw, parsed, opened⟩ := bind_ok opened
      cases opened
      have dictionaryWire := Zstd.Dictionary.V2.readDictionary_wire (mapError_ok parsed)
      have sameData : data = originalData := by
        obtain ⟨_, kind, _⟩ := dictionaryWire
        rw [order] at split
        simpa [ByteArrayFallback.splitLeading, kind] using congrArg Prod.snd split
      have pagesWire : List.Forall₂ (PageWire limits source raw) data pages :=
        ordered.imp (fun _ _ decoded => by
          obtain ⟨_, eq, wire⟩ := decodePage_wire decoded
          cases eq
          exact wire)
      exact ⟨frame, data, raw, pages, order, dictionaryAt.symm, dataAt, dictionaryWire,
        sameData.symm ▸ schedule, pagesWire, flatten, flatten ▸ (pages_count pagesWire).trans count⟩

theorem readFrames_revival {limits : Zstd.Fallback.V2.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {group column rows ordinal : Nat} {name : String} {dictionary frame : Page.Frame}
    {data : List Page.Frame} {header : Page.Dictionary} {before after : List (Page.Frame × Nat)}
    (leading : dictionary.value.kind = .dictionary header)
    (expanded : Utf8.Dictionary.Snappy.checkExpandedChunk (ε := Zstd.Fallback.V2.DecodeError)
      limits.toPhysical metadata group column name (dictionary :: data) = .ok ())
    (prefixPresent : (data.takeWhile Utf8.Fallback.isDictionaryData).isEmpty = false)
    (positions : (data.dropWhile Utf8.Fallback.isDictionaryData).zipIdx
      (1 + (data.takeWhile Utf8.Fallback.isDictionaryData).length) = before ++ (frame, ordinal) :: after)
    (earlier : before.forM (fun (item, page) => Utf8.Fallback.checkPlainTagWith.{0}
      Zstd.Fallback.V2.DecodeError.dictionaryAfterPlain group column name page item) = .ok ⟨⟩)
    (revived : Utf8.Fallback.dataEncoding frame = some 8) :
    readFrames limits metadata source group column name rows (dictionary :: data) =
      .error (.page group column name ordinal frame.header.start (.decode .dictionaryAfterPlain)) := by
  have suffixPresent : (data.dropWhile Utf8.Fallback.isDictionaryData).isEmpty = false := by
    cases h : data.dropWhile Utf8.Fallback.isDictionaryData with
    | nil => simp [h] at positions
    | cons => rfl
  have rejected : Utf8.Fallback.checkPlainTagWith.{0} Zstd.Fallback.V2.DecodeError.dictionaryAfterPlain
      group column name ordinal frame =
      .error (.page group column name ordinal frame.header.start (.decode .dictionaryAfterPlain)) := by
    simp [Utf8.Fallback.checkPlainTagWith, revived]
  have checkedPrefix : forM before (fun item => Utf8.Fallback.checkPlainTagWith.{0}
      Zstd.Fallback.V2.DecodeError.dictionaryAfterPlain group column name item.2 item.1) = .ok ⟨⟩ := by
    simpa using earlier
  have phase : Utf8.Fallback.checkPhasesWith.{0} Zstd.Fallback.V2.DecodeError.dictionaryAfterPlain
      group column name 1 data =
      .error (.page group column name ordinal frame.header.start (.decode .dictionaryAfterPlain)) := by
    simp [Utf8.Fallback.checkPhasesWith, prefixPresent, suffixPresent, positions, Bind.bind, Except.bind]
    rw [checkedPrefix, rejected]
  simp only [readFrames, expanded, ByteArrayFallback.splitLeading, leading, Bind.bind, Except.bind]
  simp only [Option.isSome_some, ite_true]
  rw [phase]

theorem readGroup_wire {parquet : Zstd.Fallback.V2.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, storedCap, decoded⟩ := ByteArrayFallback.readBoundGroupWithCodec_wire read
  have stored := Utf8.Dictionary.Snappy.storedBytes_exact located framed
  refine ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count, codec, located,
    framed, stored, ?_, readFrames_wire decoded⟩
  omega

private theorem denote_successful_prefix {name : String} {limits : Zstd.Fallback.V2.Limits}
    {checked : Snappy.Checked name} {before after : List Nat} {groups : List (List (Option Bytes))}
    (earlier : List.Forall₂ (fun index slots => readGroup limits checked index = .ok slots) before groups) :
    let tail := Reader.denoteGroups (rowsAt limits checked) after
    Reader.denoteGroups (rowsAt limits checked) (before ++ after) =
      (groups.map (Plain.ByteArray.File.rows name .optional) ++ tail.1, tail.2) := by
  induction earlier with
  | nil => rfl
  | cons decoded _ ih =>
    simp [Reader.denoteGroups, rowsAt, decoded, Except.map, ih]

theorem readAll_success {name : String} {limits : Zstd.Fallback.V2.Limits} {checked : Snappy.Checked name}
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

theorem readAll_first_error {name : String} {limits : Zstd.Fallback.V2.Limits} {checked : Snappy.Checked name}
    {before after : List Nat} {index : Nat} {groups : List (List (Option Bytes))} {cause : Zstd.Fallback.V2.GroupError}
    (split : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i slots => readGroup limits checked i = .ok slots) before groups)
    (failed : readGroup limits checked index = .error cause) :
    readAll limits checked = .ok ⟨schema name,
      ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional), .readError cause⟩⟩ := by
  rw [readAll, Reader.readAll_opened]
  simp only [source]
  rw [split, denote_successful_prefix (after := index :: after) earlier]
  simp [Reader.denoteGroups, rowsAt, failed, Except.map, List.map_map]

theorem convert_readback {parquet : Zstd.Fallback.V2.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {wire : KBytes} (written : convert parquet ipc view input name = .ok wire) :
    ∃ (checked : Snappy.Checked name) (groups : List (List (Option Bytes))) (batches : List (List (Option KBytes))),
      Snappy.openFile parquet.toPhysical input name = .ok checked ∧
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
  cases opened : Snappy.openFile parquet.toPhysical input name with
  | error cause => simp [convert, opened, Except.mapError, Bind.bind, Except.bind] at written
  | ok checked =>
    cases read : (List.range checked.physical.snapshot.groupCount).mapM (readGroup parquet checked) with
    | error cause => simp [convert, opened, read, Except.mapError, Bind.bind, Except.bind] at written
    | ok groups =>
      let source : ToIpc.Source := ⟨⟨name, true⟩, groups⟩
      have emitted : StreamWriter.emit ipc view ⟨name, true, .binary⟩ source.batches = .ok wire := by
        cases h : StreamWriter.emit ipc view ⟨name, true, .binary⟩ source.batches <;>
          simp_all [convert, source, ToIpc.Source.ipcField, Except.mapError, Bind.bind, Except.bind]
      obtain ⟨batches, decoded, values⟩ := StreamWriter.emit_binary_readback emitted
      have bytes := values.trans (ToIpc.batches_octets source)
      have counts : batches.map List.length = groups.map List.length := by
        simpa [source, List.map_map, Function.comp_def] using congrArg (List.map List.length) bytes
      have grouped := List.mapM_eq_ok_iff_forall₂.mp read
      exact ⟨checked, groups, batches, rfl, grouped.imp (fun _ _ h => readGroup_wire h),
        readAll_success grouped, decoded, bytes, counts, (Stream.read_iff _ _ _ _).mp decoded⟩

end Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2
