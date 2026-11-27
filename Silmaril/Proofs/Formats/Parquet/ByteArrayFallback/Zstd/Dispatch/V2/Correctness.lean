module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Thms
import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Thms
import Silmaril.Formats.Arrow.BinaryView.Stream.Thms
import Silmaril.Formats.Parquet.Reader.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.ByteArrayFallback hiding readGroup readFrames FramesWire
open Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2
open Silmaril.Formats.Arrow.BinaryView Silmaril.Relational

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

theorem readGroup_framed {limits : Zstd.Dispatch.V2.Limits} {name : String}
    {checked : Snappy.Checked name} {index : Nat} {group : Footer.RowGroup} {column : Footer.ColumnChunk}
    {span : Footer.Span} {frames : List Page.Frame}
    (selected : checked.physical.snapshot.groupAt index = some group)
    (fits : group.numRows.toNat ≤ limits.file.column.maxRows)
    (columnAt : group.columns[checked.physical.binding.columnOrdinal]? = some column)
    (located : ByteArrayFallback.locateForCodec .zstd limits.maxExpandedChunkBytes .rleDictionary
      limits.toPhysical.toLimits checked.physical.binding.leaf group column.metadata
      checked.physical.snapshot.footer.start = .ok span)
    (framed : Page.readChunk limits.file.column.framing checked.physical.snapshot.bytes span = .ok frames) :
    readGroup limits checked index = readFrames limits column.metadata checked.physical.snapshot.bytes
      index checked.physical.binding.columnOrdinal name group.numRows.toNat frames := by
  simp [readGroup, ByteArrayFallback.readBoundGroupWithCodec, selected, Nat.not_lt.mpr fits, columnAt, located,
    framed, Except.mapError, Bind.bind, Except.bind]

@[local simp] private theorem plain_file (limits : Zstd.Dispatch.V2.Limits) :
    (Zstd.Fallback.V2.plainLimits limits).physical.file = limits.file := rfl

@[local simp] private theorem plain_expanded (limits : Zstd.Dispatch.V2.Limits) :
    (Zstd.Fallback.V2.plainLimits limits).maxExpandedChunkBytes = limits.maxExpandedChunkBytes := rfl

@[local simp] private theorem except_throw {α ε : Type} (cause : ε) :
    (throw cause : Except ε α) = .error cause := rfl

@[local simp] private theorem plain_locate {limits : Zstd.Dispatch.V2.Limits} (leaf : Footer.SchemaElement)
    (group : Footer.RowGroup) (metadata : Footer.ColumnMetadata) (footer : Nat) :
    ByteArrayFallback.locateForCodec .zstd limits.maxExpandedChunkBytes .rleDictionary
      (Zstd.Fallback.V2.plainLimits limits).physical.toLimits leaf group metadata footer =
    ByteArrayFallback.locateForCodec .zstd limits.maxExpandedChunkBytes .rleDictionary
      limits.toPhysical.toLimits leaf group metadata footer := rfl

theorem readGroup_agrees {limits : Zstd.Dispatch.V2.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {frames : List Page.Frame} (original : FramedGroup limits checked index frames) :
    readGroup limits checked index =
      match profile frames with
      | .plain =>
        (Zstd.Plain.V2.readGroup (Zstd.Fallback.V2.plainLimits limits) checked index).mapError (liftGroupError .plain)
      | .dictionary => (Zstd.Dictionary.V2.readGroup limits checked index).mapError (liftGroupError .dictionary)
      | .fallback => (Zstd.Fallback.V2.readGroup limits checked index).mapError (liftGroupError .fallback) := by
  obtain ⟨group, column, span, selected, columnAt, located, framed⟩ := original
  by_cases cap : limits.file.column.maxRows < group.numRows.toNat
  · cases chosen : profile frames <;>
      simp [readGroup, Zstd.Plain.V2.readGroup, Zstd.Dictionary.V2.readGroup, Zstd.Fallback.V2.readGroup,
        ByteArrayFallback.readBoundGroupWithCodec, selected, cap, Except.mapError, liftGroupError]
  cases chosen : profile frames <;>
    simp [readGroup, Zstd.Plain.V2.readGroup, Zstd.Dictionary.V2.readGroup, Zstd.Fallback.V2.readGroup,
      ByteArrayFallback.readBoundGroupWithCodec, selected, cap, columnAt, located,
      framed, readFrames, chosen, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_unframed_agrees {limits : Zstd.Dispatch.V2.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} (unframed : ∀ frames, ¬ FramedGroup limits checked index frames) :
    readGroup limits checked index =
      (Zstd.Plain.V2.readGroup (Zstd.Fallback.V2.plainLimits limits) checked index).mapError (liftGroupError .plain) ∧
    readGroup limits checked index =
      (Zstd.Dictionary.V2.readGroup limits checked index).mapError (liftGroupError .dictionary) ∧
    readGroup limits checked index =
      (Zstd.Fallback.V2.readGroup limits checked index).mapError (liftGroupError .fallback) := by
  unfold readGroup Zstd.Plain.V2.readGroup Zstd.Dictionary.V2.readGroup Zstd.Fallback.V2.readGroup
    ByteArrayFallback.readBoundGroupWithCodec
  cases selected : checked.physical.snapshot.groupAt index with
  | none => simp [Except.mapError, liftGroupError]
  | some group =>
    by_cases cap : limits.file.column.maxRows < group.numRows.toNat
    · simp [cap, Except.mapError, liftGroupError]
    cases columnAt : group.columns[checked.physical.binding.columnOrdinal]? with
    | none => simp [cap, columnAt, Except.mapError, liftGroupError]
    | some column =>
      cases located : ByteArrayFallback.locateForCodec .zstd limits.maxExpandedChunkBytes .rleDictionary
          limits.toPhysical.toLimits checked.physical.binding.leaf group column.metadata
          checked.physical.snapshot.footer.start with
      | error cause => simp [cap, columnAt, located, Except.mapError, liftGroupError, Bind.bind, Except.bind]
      | ok span =>
        cases framed : Page.readChunk limits.file.column.framing checked.physical.snapshot.bytes span with
        | error cause =>
          simp [cap, columnAt, located, framed, Except.mapError, liftGroupError, Bind.bind, Except.bind]
        | ok frames => exact False.elim (unframed frames ⟨group, column, span, selected, columnAt, located, framed⟩)

theorem readFrames_wire {limits : Zstd.Dispatch.V2.Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots := by
  cases chosen : profile frames with
  | plain => exact (by simpa only [FramesWire, chosen] using
      Zstd.Plain.V2.readFrames_wire (mapError_ok (by simpa only [readFrames, chosen] using read)))
  | dictionary => exact (by simpa only [FramesWire, chosen] using
      Zstd.Dictionary.V2.readFrames_wire (mapError_ok (by simpa only [readFrames, chosen] using read)))
  | fallback => exact (by simpa only [FramesWire, chosen] using
      Zstd.Fallback.V2.readFrames_wire (mapError_ok (by simpa only [readFrames, chosen] using read)))

theorem readGroup_wire {parquet : Zstd.Dispatch.V2.Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, storedCap, decoded⟩ := ByteArrayFallback.readBoundGroupWithCodec_wire read
  have stored := Utf8.Dictionary.Snappy.storedBytes_exact located framed
  refine ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count, codec, located,
    framed, stored, ?_, readFrames_wire decoded⟩
  omega

private theorem denote_successful_prefix {name : String} {limits : Zstd.Dispatch.V2.Limits}
    {checked : Snappy.Checked name} {before after : List Nat} {groups : List (List (Option Bytes))}
    (earlier : List.Forall₂ (fun index slots => readGroup limits checked index = .ok slots) before groups) :
    let tail := Reader.denoteGroups (rowsAt limits checked) after
    Reader.denoteGroups (rowsAt limits checked) (before ++ after) =
      (groups.map (Plain.ByteArray.File.rows name .optional) ++ tail.1, tail.2) := by
  induction earlier with
  | nil => rfl
  | cons decoded _ ih =>
    simp [Reader.denoteGroups, rowsAt, decoded, Except.map, ih]

theorem readAll_success {name : String} {limits : Zstd.Dispatch.V2.Limits} {checked : Snappy.Checked name}
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

theorem readAll_first_error {name : String} {limits : Zstd.Dispatch.V2.Limits} {checked : Snappy.Checked name}
    {before after : List Nat} {index : Nat} {groups : List (List (Option Bytes))} {cause : Zstd.Dispatch.V2.GroupError}
    (split : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i slots => readGroup limits checked i = .ok slots) before groups)
    (failed : readGroup limits checked index = .error cause) :
    readAll limits checked = .ok ⟨schema name,
      ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional), .readError cause⟩⟩ := by
  rw [readAll, Reader.readAll_opened]
  simp only [source]
  rw [split, denote_successful_prefix (after := index :: after) earlier]
  simp [Reader.denoteGroups, rowsAt, failed, Except.map, List.map_map]

theorem convert_readback {parquet : Zstd.Dispatch.V2.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
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

end Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2
