module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Fallback

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.ByteArrayFallback
open Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback
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

private theorem decodePlainPage_wire {limits : Gzip.Fallback.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePlainPage limits metadata source frame = .ok slots) :
    PlainPageWire limits source frame slots := by
  unfold decodePlainPage at read
  split at read <;> try contradiction
  rename_i header kind
  split at read <;> try contradiction
  rename_i tag
  exact ⟨⟨header, kind, tag⟩, Utf8.Fallback.Snappy.decodePlainBytesWith_wire (mapError_ok read)⟩

theorem decodePage_wire {limits : Gzip.Fallback.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {dictionary : Option (Array Bytes)} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePage limits metadata source dictionary frame = .ok slots) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame slots := by
  cases dictionary with
  | none => contradiction
  | some entries =>
    simp only [decodePage] at read
    split at read
    · exact ⟨entries, rfl, .inr (decodePlainPage_wire read)⟩
    · obtain ⟨_, same, wire⟩ := Gzip.Dictionary.decodePage_wire read
      cases same
      exact ⟨entries, rfl, .inl wire⟩

theorem data_member {limits : Gzip.Fallback.Limits} {source : Bytes} {entries : Array Bytes}
    {frame : Page.Frame} {slots : List (Option Bytes)} (wire : PageWire limits source entries frame slots) :
    ∃ expanded,
      Compression.Gzip.decoder (Page.Checksum.payloadBytes source frame).toList = some (expanded, []) ∧
      expanded.length = frame.value.uncompressedSize := by
  rcases wire with dictionary | ⟨⟨header, kind, _⟩, params, _, _, original, _, _, _, prepared, _, _, _⟩
  · exact Gzip.Dictionary.data_member dictionary
  · simp only [FlatColumn.pageParameters, kind, Option.some.injEq] at original
    subst params
    exact ScalarPage.prepared_v1_gzip_member rfl rfl prepared

theorem frames_members {limits : Gzip.Fallback.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {rows : Nat} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (wire : FramesWire limits metadata source rows frames slots) (frame : Page.Frame) (present : frame ∈ frames) :
    ∃ expanded,
      Compression.Gzip.decoder (Page.Checksum.payloadBytes source frame).toList = some (expanded, []) ∧
      expanded.length = frame.value.uncompressedSize := by
  obtain ⟨_, _, dictionary, data, entries, pages, rfl, _, _, leading, _, ordered, _, _⟩ := wire
  rcases List.mem_cons.mp present with rfl | present
  · have member := Gzip.Dictionary.dictionary_member leading
    obtain ⟨_, expanded, _, _, _, _, _, size, _, bytes, _⟩ := leading
    exact ⟨expanded, bytes.symm ▸ member, size⟩
  · have members := ordered.imp (fun _ _ page => And.intro (data_member page) page)
    exact ((List.forall₂_and_left data pages).mp members).1 frame present

private theorem pages_count {limits : Gzip.Fallback.Limits} {source : Bytes}
    {entries : Array Bytes} {frames : List Page.Frame} {pages : List (List (Option Bytes))}
    (ordered : List.Forall₂ (PageWire limits source entries) frames pages) :
    pages.flatten.length = (frames.map ByteArrayFallback.declaredSlots).sum := by
  induction ordered with
  | nil => rfl
  | cons wire _ ih =>
    have count := match wire with
      | .inl ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, count⟩ => count
      | .inr ⟨_, _, _, _, _, _, _, _, _, _, _, count⟩ => count
    simp [count, ih]

private theorem readFrames_wire {limits : Gzip.Fallback.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots := by
  unfold ByteArrayFallback.Gzip.Fallback.readFrames at read
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
      have dictionaryWire := Gzip.Dictionary.readDictionary_wire parsed
      have sameData : data = originalData := by
        obtain ⟨_, _, kind, _⟩ := dictionaryWire
        rw [order] at split
        simpa [ByteArrayFallback.splitLeading, kind] using congrArg Prod.snd split
      have pagesWire : List.Forall₂ (PageWire limits source raw) data pages :=
        ordered.imp (fun _ _ decoded => by
          obtain ⟨_, eq, wire⟩ := decodePage_wire decoded
          cases eq
          exact wire)
      exact ⟨frame, data, raw, pages, order, dictionaryAt.symm, dataAt, dictionaryWire,
        sameData.symm ▸ schedule, pagesWire, flatten, flatten ▸ (pages_count pagesWire).trans count⟩

theorem readGroup_wire {parquet : Gzip.Fallback.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, storedCap, decoded⟩ := ByteArrayFallback.readBoundGroupWithCodec_wire read
  have stored := Utf8.Dictionary.Snappy.storedBytes_exact located framed
  refine ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count, codec, located,
    framed, stored, ?_, readFrames_wire decoded⟩
  omega

theorem convert_readback {parquet : Gzip.Fallback.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {wire : KBytes} (written : convert parquet ipc view input name = .ok wire) :
    ∃ (checked : Snappy.Checked name) (groups : List (List (Option Bytes))) (batches : List (List (Option KBytes))),
      Snappy.openFile parquet.toSnappyLimits input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc view wire = .ok ⟨⟨name, true, .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) = groups.map (List.map (Option.map Bytes.toList)) ∧
      batches.map List.length = groups.map List.length ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchema ipc wire = .ok (⟨name, true, .binary⟩, start) ∧
        Stream.BatchesWire ipc view wire ⟨name, true, .binary⟩ ipc.batches start batches := by
  obtain ⟨checked, groups, batches, opened, read, decoded, bytes, counts, extent⟩ := Snappy.convertWith_readback written
  exact ⟨checked, groups, batches, opened,
    (List.mapM_eq_ok_iff_forall₂.mp read).imp (fun _ _ h => readGroup_wire h), decoded, bytes, counts, extent⟩

end Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Fallback
