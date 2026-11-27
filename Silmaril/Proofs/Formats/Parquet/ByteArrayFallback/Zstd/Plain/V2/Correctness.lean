module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.FlatColumn.Zstd.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Thms
import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Thms
import Silmaril.Formats.Arrow.BinaryView.Stream.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.ByteArrayFallback hiding readGroup readFrames FramesWire PageWire
open Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2
open Silmaril.Formats.Arrow.BinaryView

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β}
    {out : β} (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ}
    {out : α} (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

theorem decodePage_wire {limits : Zstd.Plain.V2.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePage limits metadata source frame = .ok slots) : PageWire limits source frame slots := by
  cases kind : frame.value.kind with
  | dataV1 _ | dictionary _ | skipped _ => simp [decodePage, kind] at read
  | dataV2 data =>
    simp only [decodePage, kind] at read
    split at read <;> try contradiction
    rename_i tag
    split at read <;> try contradiction
    obtain ⟨status, verified, read⟩ := bind_ok read
    simp only [FlatColumn.pageParameters, kind] at read
    obtain ⟨page, prepared, read⟩ := bind_ok read
    obtain ⟨values, parsed, read⟩ := bind_ok read
    obtain ⟨_, layout, _, _, _, expandedCap, preparedWire⟩ :=
      FlatColumn.Zstd.prepareFor_sound (mapError_ok prepared)
    simp only [FlatColumn.Zstd.PreparedWire] at preparedWire
    obtain ⟨nulls, rows, repetitions, storedFits, expandedFits, defCap, definitions, encoded, width, split,
      levels, presentCount, payload⟩ := preparedWire
    obtain ⟨mask, ordered⟩ := FlatPage.reconstruct_ok_iff.mp (mapError_ok read)
    obtain ⟨_, bytes, _, _⟩ := Plain.ByteArray.decode_ok_iff.mp (mapError_ok parsed)
    have count := congrArg List.length mask
    rw [List.length_map, FlatPage.readMask_length levels] at count
    refine ⟨Utf8.Dictionary.Snappy.stored_wire (mapError_ok verified), expandedCap,
      data, layout, definitions, encoded, kind, not_not.mp tag, repetitions, rows, nulls,
      storedFits, expandedFits, defCap, width, split, ?_, ?_, count, ?_⟩
    · rw [mask]
      exact levels
    · rw [mask]
      exact presentCount
    · rwa [ordered, ← bytes]

private theorem pages_count {limits : Zstd.Plain.V2.Limits} {source : Bytes}
    {frames : List Page.Frame} {pages : List (List (Option Bytes))}
    (ordered : List.Forall₂ (PageWire limits source) frames pages) :
    pages.flatten.length = (frames.map ByteArrayFallback.declaredSlots).sum := by
  induction ordered with
  | nil => rfl
  | cons wire _ ih =>
    obtain ⟨_, _, data, _, _, _, kind, _, _, _, _, _, _, _, _, _, _, _, count, _⟩ := wire
    simp [count, ih, ByteArrayFallback.declaredSlots, FlatColumn.pageParameters, kind]

theorem readFrames_wire {limits : Zstd.Plain.V2.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
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

theorem readGroup_wire {parquet : Zstd.Plain.V2.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, storedCap, decoded⟩ := ByteArrayFallback.readBoundGroupWithCodec_wire read
  have stored := Utf8.Dictionary.Snappy.storedBytes_exact located framed
  refine ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count, codec, located,
    framed, stored, ?_, readFrames_wire decoded⟩
  change column.metadata.totalCompressedSize ≤ (parquet.file.column.maxChunkBytes : Int) at storedCap
  omega

theorem convert_readback {parquet : Zstd.Plain.V2.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {wire : KBytes} (written : convert parquet ipc view input name = .ok wire) :
    ∃ (checked : Snappy.Checked name) (groups : List (List (Option Bytes))) (batches : List (List (Option KBytes))),
      Snappy.openFile parquet.physical input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc view wire = .ok ⟨⟨name, true, .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) = groups.map (List.map (Option.map Bytes.toList)) ∧
      batches.map List.length = groups.map List.length ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchema ipc wire = .ok (⟨name, true, .binary⟩, start) ∧
        Stream.BatchesWire ipc view wire ⟨name, true, .binary⟩ ipc.batches start batches := by
  cases opened : Snappy.openFile parquet.physical input name with
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

end Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2
