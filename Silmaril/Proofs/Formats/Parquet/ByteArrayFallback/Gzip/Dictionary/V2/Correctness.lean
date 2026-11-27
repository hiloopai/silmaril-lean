module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.V2.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Payload.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.V2

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.ByteArrayFallback
open Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.V2
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

theorem decodePage_wire {limits : Gzip.Dictionary.V2.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {dictionary : Option (Array Bytes)} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodePage limits metadata source dictionary frame = .ok slots) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame slots := by
  unfold decodePage at read
  split at read <;> try contradiction
  rename_i header kind
  split at read <;> try contradiction
  rename_i tag
  obtain ⟨entries, found, wire⟩ := Utf8.Dictionary.Snappy.decodeIndexPageWith_wire (mapError_ok read)
  exact ⟨entries, found, ⟨header, kind, tag⟩, wire⟩

theorem data_suffix {limits : Gzip.Dictionary.V2.Limits} {source : Bytes} {entries : Array Bytes}
    {frame : Page.Frame} {slots : List (Option Bytes)} (wire : PageWire limits source entries frame slots) :
    SuffixWire limits source entries frame slots := by
  obtain ⟨⟨header, kind, tag⟩, params, layout, page, indices, original, _, _, _, _, prepared, parsed, lookedUp, mask, _⟩ := wire
  simp only [FlatColumn.pageParameters, kind, Option.some.injEq] at original
  subst params
  obtain ⟨_, _, repetition, storedFits, expandedFits, _, definitions, encoded, width, split, levels, presentCount, payload⟩ :=
    prepared
  obtain ⟨storedSize, expandedSize, codec, selected, decoded⟩ := payload
  refine ⟨header, layout, definitions, encoded, page.scalars, indices, kind, tag, repetition, storedFits, expandedFits,
    width, split, ?_, ?_, storedSize, expandedSize, ?_, ?_, lookedUp⟩
  · rw [mask]
    exact levels
  · rw [mask]
    exact presentCount
  · cases flag : header.isCompressed
    · simp only [ScalarPage.v2Codec, flag, Option.getD_some, Bool.false_eq_true, ↓reduceIte,
        Payload.Codec.ofId_id, Option.some.injEq] at selected
      subst codec
      cases decoded
      rfl
    · simp only [ScalarPage.v2Codec, flag, Option.getD_some, ↓reduceIte,
        Payload.Codec.ofId_id, Option.some.injEq] at selected
      subst codec
      cases decoded with
      | gzip member => simpa only [flag, ↓reduceIte] using member
  · rw [mask]
    exact parsed

private theorem pages_count {limits : Gzip.Dictionary.V2.Limits} {source : Bytes}
    {entries : Array Bytes} {frames : List Page.Frame} {pages : List (List (Option Bytes))}
    (ordered : List.Forall₂ (PageWire limits source entries) frames pages) :
    pages.flatten.length = (frames.map ByteArrayFallback.declaredSlots).sum := by
  induction ordered with
  | nil => rfl
  | cons wire _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, count⟩ := wire
    simp [count, ih]

theorem readFrames_wire {limits : Gzip.Dictionary.V2.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots := by
  unfold ByteArrayFallback.Gzip.Dictionary.V2.readFrames at read
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
    exact ⟨frame, data, raw, pages, order, dictionaryAt.symm, dataAt, Gzip.Dictionary.readDictionary_wire parsed,
      pagesWire, flatten, flatten ▸ (pages_count pagesWire).trans count⟩

theorem readGroup_wire {parquet : Gzip.Dictionary.V2.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, storedCap, decoded⟩ := ByteArrayFallback.readBoundGroupWithCodec_wire read
  have stored := Utf8.Dictionary.Snappy.storedBytes_exact located framed
  refine ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count, codec, located,
    framed, stored, ?_, readFrames_wire decoded⟩
  omega

theorem convert_readback {parquet : Gzip.Dictionary.V2.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
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

end Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.V2
