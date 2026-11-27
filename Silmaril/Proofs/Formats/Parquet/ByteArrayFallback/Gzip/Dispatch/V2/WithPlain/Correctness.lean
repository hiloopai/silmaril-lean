module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dictionary.V2.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Fallback.V2.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Plain.V2.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.ByteArrayFallback hiding readGroup readFrames FramesWire
open Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain
open Silmaril.Formats.Arrow.BinaryView

theorem readGroup_framed {limits : Gzip.Dispatch.V2.WithPlain.Limits} {name : String}
    {checked : Snappy.Checked name} {index : Nat} {group : Footer.RowGroup} {column : Footer.ColumnChunk}
    {span : Footer.Span} {frames : List Page.Frame}
    (selected : checked.physical.snapshot.groupAt index = some group)
    (fits : group.numRows.toNat ≤ limits.file.column.maxRows)
    (columnAt : group.columns[checked.physical.binding.columnOrdinal]? = some column)
    (located : ByteArrayFallback.locateForCodec .gzip limits.maxExpandedChunkBytes .rleDictionary
      limits.toSnappyLimits.toLimits checked.physical.binding.leaf group column.metadata
      checked.physical.snapshot.footer.start = .ok span)
    (framed : Page.readChunk limits.file.column.framing checked.physical.snapshot.bytes span = .ok frames) :
    readGroup limits checked index = readFrames limits column.metadata checked.physical.snapshot.bytes
      index checked.physical.binding.columnOrdinal name group.numRows.toNat frames := by
  simp [readGroup, ByteArrayFallback.readBoundGroupWithCodec, selected, Nat.not_lt.mpr fits, columnAt, located,
    framed, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_agrees {limits : Gzip.Dispatch.V2.WithPlain.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {frames : List Page.Frame} (original : Gzip.Dispatch.FramedGroup limits checked index frames) :
    readGroup limits checked index =
      match profile frames with
      | .plain => Gzip.Plain.V2.readGroup limits checked index
      | .dictionary => Gzip.Dictionary.V2.readGroup limits checked index
      | .fallback => Gzip.Fallback.V2.readGroup limits checked index := by
  obtain ⟨group, column, span, selected, columnAt, located, framed⟩ := original
  cases chosen : profile frames <;>
    simp [readGroup, Gzip.Plain.V2.readGroup, Gzip.Dictionary.V2.readGroup, Gzip.Fallback.V2.readGroup,
      ByteArrayFallback.readBoundGroupWithCodec,
      selected, columnAt, located, framed, readFrames, chosen, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_unframed_agrees {limits : Gzip.Dispatch.V2.WithPlain.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} (unframed : ∀ frames, ¬ Gzip.Dispatch.FramedGroup limits checked index frames) :
    readGroup limits checked index = Gzip.Plain.V2.readGroup limits checked index ∧
      readGroup limits checked index = Gzip.Dictionary.V2.readGroup limits checked index ∧
      readGroup limits checked index = Gzip.Fallback.V2.readGroup limits checked index := by
  unfold readGroup Gzip.Plain.V2.readGroup Gzip.Dictionary.V2.readGroup Gzip.Fallback.V2.readGroup
    ByteArrayFallback.readBoundGroupWithCodec
  cases selected : checked.physical.snapshot.groupAt index with
  | none => simp
  | some group =>
    by_cases cap : limits.file.column.maxRows < group.numRows.toNat
    · simp [cap]
    cases columnAt : group.columns[checked.physical.binding.columnOrdinal]? with
    | none => simp [cap, columnAt]
    | some column =>
      cases located : ByteArrayFallback.locateForCodec .gzip limits.maxExpandedChunkBytes .rleDictionary
          limits.toSnappyLimits.toLimits checked.physical.binding.leaf group column.metadata
          checked.physical.snapshot.footer.start with
      | error cause => simp [cap, columnAt, located, Except.mapError, Bind.bind, Except.bind]
      | ok span =>
        cases framed : Page.readChunk limits.file.column.framing checked.physical.snapshot.bytes span with
        | error cause => simp [cap, columnAt, located, framed, Except.mapError, Bind.bind, Except.bind]
        | ok frames => exact False.elim (unframed frames ⟨group, column, span, selected, columnAt, located, framed⟩)

theorem readFrames_wire {limits : Gzip.Dispatch.V2.WithPlain.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots := by
  cases chosen : profile frames with
  | plain => exact (by simpa only [FramesWire, chosen] using
      Gzip.Plain.V2.readFrames_wire (by simpa only [readFrames, chosen] using read))
  | dictionary => exact (by simpa only [FramesWire, chosen] using
      Gzip.Dictionary.V2.readFrames_wire (by simpa only [readFrames, chosen] using read))
  | fallback => exact (by simpa only [FramesWire, chosen] using
      Gzip.Fallback.V2.readFrames_wire (by simpa only [readFrames, chosen] using read))

theorem readGroup_wire {parquet : Gzip.Dispatch.V2.WithPlain.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, storedCap, decoded⟩ := ByteArrayFallback.readBoundGroupWithCodec_wire read
  have stored := Utf8.Dictionary.Snappy.storedBytes_exact located framed
  refine ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count, codec, located,
    framed, stored, ?_, readFrames_wire decoded⟩
  omega

theorem convert_readback {parquet : Gzip.Dispatch.V2.WithPlain.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
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

end Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain
