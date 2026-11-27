module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Parquet.FlatColumn.Zstd.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Thms
import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Thms
import Silmaril.Formats.Arrow.BinaryView.Stream.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.ByteArrayFallback hiding readDictionary readGroup readFrames FramesWire PageWire
open Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2
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

theorem readDictionary_wire {limits : Zstd.Dictionary.V2.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {frame : Page.Frame} {entries : Array Bytes}
    (read : readDictionary limits metadata source frame = .ok entries) :
    DictionaryWire limits source frame entries := by
  cases kind : frame.value.kind with
  | dataV1 _ | dataV2 _ | skipped _ => simp [readDictionary, kind] at read
  | dictionary header =>
    simp only [readDictionary, kind] at read
    split at read <;> try contradiction
    rename_i tag
    split at read <;> try contradiction
    split at read <;> try contradiction
    rename_i cap
    obtain ⟨_, verified, read⟩ := bind_ok read
    obtain ⟨expanded, decoded, read⟩ := bind_ok read
    obtain ⟨values, parsed, read⟩ := bind_ok read
    cases read
    obtain ⟨_, octets, count, _⟩ := Plain.ByteArray.decode_ok_iff.mp (mapError_ok parsed)
    simp only [Bytes.toList_ofList] at octets
    refine ⟨header, kind, not_not.mp tag, Nat.le_of_not_gt cap, by simpa using count,
      Utf8.Dictionary.Snappy.stored_wire (mapError_ok verified), ?_⟩
    rw [List.toList_toArray, ← octets]
    exact FlatColumn.Zstd.decodePayload_sound (mapError_ok decoded)

theorem decodePage_wire {limits : Zstd.Dictionary.V2.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {dictionary : Option (Array Bytes)} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePage limits metadata source dictionary frame = .ok slots) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame slots := by
  cases kind : frame.value.kind with
  | dataV1 _ | dictionary _ | skipped _ => simp [decodePage, kind] at read
  | dataV2 data =>
    simp only [decodePage, kind] at read
    split at read <;> try contradiction
    rename_i tag
    split at read <;> try contradiction
    cases dictionary with
    | none => contradiction
    | some entries =>
      obtain ⟨_, verified, read⟩ := bind_ok read
      simp only [FlatColumn.pageParameters, kind] at read
      obtain ⟨page, prepared, read⟩ := bind_ok read
      obtain ⟨indices, parsed, read⟩ := bind_ok read
      obtain ⟨values, selected, read⟩ := bind_ok read
      obtain ⟨_, layout, _, _, _, expandedCap, preparedWire⟩ :=
        FlatColumn.Zstd.prepareFor_sound (mapError_ok prepared)
      obtain ⟨nulls, rows, repetitions, storedFits, expandedFits, defCap, definitions, encoded, width, split,
        levels, presentCount, payload⟩ := preparedWire
      obtain ⟨mask, ordered⟩ := FlatPage.reconstruct_ok_iff.mp (mapError_ok read)
      have count := congrArg List.length mask
      rw [List.length_map, FlatPage.readMask_length levels] at count
      refine ⟨entries, rfl, Utf8.Dictionary.Snappy.stored_wire (mapError_ok verified), expandedCap,
        data, layout, definitions, encoded, page.scalars, indices, kind, not_not.mp tag, repetitions, rows, nulls,
        storedFits, expandedFits, defCap, width, split, ?_, ?_, count, payload, ?_, ?_⟩
      · rwa [mask]
      · rwa [mask]
      · rw [mask]
        exact mapError_ok parsed
      · rw [ordered]
        exact DictionaryIndex.select_ok_iff.mp (mapError_ok selected)

private theorem pages_count {limits : Zstd.Dictionary.V2.Limits} {source : Bytes} {entries : Array Bytes}
    {frames : List Page.Frame} {pages : List (List (Option Bytes))}
    (ordered : List.Forall₂ (PageWire limits source entries) frames pages) :
    pages.flatten.length = (frames.map ByteArrayFallback.declaredSlots).sum := by
  induction ordered with
  | nil => rfl
  | cons wire _ ih =>
    obtain ⟨_, _, data, _, _, _, _, _, kind, _, _, _, _, _, _, _, _, _, _, _, count, _⟩ := wire
    simp [count, ih, ByteArrayFallback.declaredSlots, FlatColumn.pageParameters, kind]

theorem readFrames_wire {limits : Zstd.Dictionary.V2.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots := by
  unfold ByteArrayFallback.Zstd.Dictionary.V2.readFrames at read
  obtain ⟨_, checked, read⟩ := bind_ok read
  have ⟨fits, size⟩ := Utf8.Dictionary.Snappy.checkExpandedChunk_wire checked
  refine ⟨fits, size, ?_⟩
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
    have pagesWire : List.Forall₂ (PageWire limits source raw) data pages :=
      ordered.imp (fun _ _ decoded => by
        obtain ⟨_, eq, wire⟩ := decodePage_wire decoded
        cases eq
        exact wire)
    exact ⟨frame, data, raw, pages, order, dictionaryAt.symm, dataAt, readDictionary_wire parsed,
      pagesWire, flatten, flatten ▸ (pages_count pagesWire).trans count⟩

theorem readFrames_first_page_error {limits : Zstd.Dictionary.V2.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {group column rows ordinal : Nat} {name : String} {dictionary frame : Page.Frame}
    {data : List Page.Frame} {header : Page.Dictionary} {entries : Array Bytes}
    {before after : List (Page.Frame × Nat)} {prefixSlots : List (List (Option Bytes))}
    {cause : FlatColumn.PageError Zstd.Dictionary.V2.DecodeError}
    (kind : dictionary.value.kind = .dictionary header)
    (expanded : Utf8.Dictionary.Snappy.checkExpandedChunk (ε := Zstd.Dictionary.V2.DecodeError)
      limits.toPhysical metadata group column name (dictionary :: data) = .ok ())
    (dictionaryAt : metadata.dictionaryPageOffset = some (dictionary.header.start : Int))
    (dataAt : data.head?.map (fun page : Page.Frame => (page.header.start : Int)) = some metadata.dataPageOffset)
    (count : (data.map ByteArrayFallback.declaredSlots).sum = rows)
    (opened : readDictionary limits metadata source dictionary = .ok entries)
    (split : data.zipIdx 1 = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, page) => (decodePage limits metadata source (some entries) item).mapError
      (FlatColumn.Error.page group column name page item.header.start)) = .ok prefixSlots)
    (failed : decodePage limits metadata source (some entries) frame = .error cause) :
    readFrames limits metadata source group column name rows (dictionary :: data) =
      .error (.page group column name ordinal frame.header.start cause) := by
  simp only [Except.mapError] at earlier
  simp [readFrames, expanded, ByteArrayFallback.readFramesWith, ByteArrayFallback.splitLeading, kind,
    dictionaryAt, dataAt, count, opened, split, List.mapM_append, earlier, List.mapM_cons, failed,
    Except.mapError, Bind.bind, Except.bind]

theorem readGroup_wire {parquet : Zstd.Dictionary.V2.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, storedCap, decoded⟩ := ByteArrayFallback.readBoundGroupWithCodec_wire read
  have stored := Utf8.Dictionary.Snappy.storedBytes_exact located framed
  refine ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count, codec, located,
    framed, stored, ?_, readFrames_wire decoded⟩
  omega

theorem convert_readback {parquet : Zstd.Dictionary.V2.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {wire : KBytes} (written : convert parquet ipc view input name = .ok wire) :
    ∃ (checked : Snappy.Checked name) (groups : List (List (Option Bytes))) (batches : List (List (Option KBytes))),
      Snappy.openFile parquet.toPhysical input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
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
      exact ⟨checked, groups, batches, rfl, (List.mapM_eq_ok_iff_forall₂.mp read).imp
          (fun _ _ h => readGroup_wire h), decoded, bytes, counts, (Stream.read_iff _ _ _ _).mp decoded⟩

end Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2
