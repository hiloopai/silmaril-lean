module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Plain.V2.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.V2.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Plain.V2

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.ByteArrayFallback hiding readGroup readFrames FramesWire PageWire
open Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Plain.V2
open Silmaril.Formats.Arrow.BinaryView

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β}
    {out : β} (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem pages_count {limits : Gzip.Plain.V2.Limits} {source : Bytes}
    {frames : List Page.Frame} {pages : List (List (Option Bytes))}
    (ordered : List.Forall₂ (PageWire limits source) frames pages) :
    pages.flatten.length = (frames.map ByteArrayFallback.declaredSlots).sum := by
  induction ordered with
  | nil => rfl
  | cons wire _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, count⟩ := wire
    simp [count, ih]

theorem readFrames_wire {limits : Gzip.Plain.V2.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
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
    have pagesWire := ordered.imp (fun _ _ decoded => Gzip.Fallback.V2.decodePlainPage_wire decoded)
    exact ⟨fits, exactSize, dictionaryAt.symm, dataAt, pages, pagesWire, flatten,
      flatten ▸ (pages_count pagesWire).trans count⟩

theorem readGroup_wire {parquet : Gzip.Plain.V2.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, storedCap, decoded⟩ := ByteArrayFallback.readBoundGroupWithCodec_wire read
  have stored := Utf8.Dictionary.Snappy.storedBytes_exact located framed
  refine ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count, codec, located,
    framed, stored, ?_, readFrames_wire decoded⟩
  omega

theorem convert_readback {parquet : Gzip.Plain.V2.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
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

end Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Plain.V2
