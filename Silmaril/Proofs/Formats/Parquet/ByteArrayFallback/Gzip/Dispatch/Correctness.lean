module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.ByteArrayFallback hiding readGroup readFrames FramesWire
open Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch
open Silmaril.Formats.Arrow.BinaryView

theorem readGroup_agrees {limits : Gzip.Dispatch.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {frames : List Page.Frame} (original : FramedGroup limits checked index frames) :
    readGroup limits checked index =
      match profile frames with
      | .dictionary => Gzip.Dictionary.readGroup limits checked index
      | .fallback => Gzip.Fallback.readGroup limits checked index := by
  obtain ⟨group, column, span, selected, columnAt, located, framed⟩ := original
  cases chosen : profile frames <;>
    simp [readGroup, Gzip.Dictionary.readGroup, Gzip.Fallback.readGroup, ByteArrayFallback.readBoundGroupWithCodec,
      selected, columnAt, located, framed, readFrames, chosen, Except.mapError, Bind.bind, Except.bind]

theorem readFrames_wire {limits : Gzip.Dispatch.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots := by
  cases chosen : profile frames with
  | dictionary => exact (by simpa only [FramesWire, chosen] using
      Gzip.Dictionary.readFrames_wire (by simpa only [readFrames, chosen] using read))
  | fallback => exact (by simpa only [FramesWire, chosen] using
      Gzip.Fallback.readFrames_wire (by simpa only [readFrames, chosen] using read))

theorem frames_members {limits : Gzip.Dispatch.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {rows : Nat} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (wire : FramesWire limits metadata source rows frames slots) (frame : Page.Frame) (present : frame ∈ frames) :
    ∃ expanded,
      Compression.Gzip.decoder (Page.Checksum.payloadBytes source frame).toList = some (expanded, []) ∧
      expanded.length = frame.value.uncompressedSize := by
  cases chosen : profile frames with
  | fallback =>
    exact Gzip.Fallback.frames_members (by simpa only [FramesWire, chosen] using wire) frame present
  | dictionary =>
    simp only [FramesWire, chosen] at wire
    obtain ⟨_, _, dictionary, data, entries, pages, order, _, _, leading, ordered, _, _⟩ := wire
    rw [order] at present
    rcases List.mem_cons.mp present with rfl | present
    · have member := Gzip.Dictionary.dictionary_member leading
      obtain ⟨_, expanded, _, _, _, _, _, size, _, bytes, _⟩ := leading
      exact ⟨expanded, bytes.symm ▸ member, size⟩
    · have members := ordered.imp (fun _ _ page => And.intro (Gzip.Dictionary.data_member page) page)
      exact ((List.forall₂_and_left data pages).mp members).1 frame present

theorem readGroup_wire {parquet : Gzip.Dispatch.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, storedCap, decoded⟩ := ByteArrayFallback.readBoundGroupWithCodec_wire read
  have stored := Utf8.Dictionary.Snappy.storedBytes_exact located framed
  refine ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count, codec, located,
    framed, stored, ?_, readFrames_wire decoded⟩
  omega

theorem convert_readback {parquet : Gzip.Dispatch.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
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

end Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch
