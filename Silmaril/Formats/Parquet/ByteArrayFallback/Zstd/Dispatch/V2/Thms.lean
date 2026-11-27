module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2.Defs
import Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2.Correctness

public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2

open Arrow.BinaryView
open Plain.ByteArray
open Silmaril.Relational

/-- The original selected chunk is framed once and supplied unchanged to the dispatcher. -/
theorem readGroup_framed {limits : Limits} {name : String}
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
      index checked.physical.binding.columnOrdinal name group.numRows.toNat frames :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2.readGroup_framed selected fits columnAt located framed

/-- The selected strict group reader agrees on exact slots and structured failures. -/
theorem readGroup_agrees {limits : Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {frames : List Page.Frame} (original : FramedGroup limits checked index frames) :
    readGroup limits checked index =
      match profile frames with
      | .plain =>
        (Zstd.Plain.V2.readGroup (Zstd.Fallback.V2.plainLimits limits) checked index).mapError (liftGroupError .plain)
      | .dictionary => (Zstd.Dictionary.V2.readGroup limits checked index).mapError (liftGroupError .dictionary)
      | .fallback => (Zstd.Fallback.V2.readGroup limits checked index).mapError (liftGroupError .fallback) :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2.readGroup_agrees original

/-- Before framing succeeds, all three strict readers agree on admission failures. -/
theorem readGroup_unframed_agrees {limits : Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} (unframed : ∀ frames, ¬ FramedGroup limits checked index frames) :
    readGroup limits checked index =
      (Zstd.Plain.V2.readGroup (Zstd.Fallback.V2.plainLimits limits) checked index).mapError (liftGroupError .plain) ∧
    readGroup limits checked index =
      (Zstd.Dictionary.V2.readGroup limits checked index).mapError (liftGroupError .dictionary) ∧
    readGroup limits checked index =
      (Zstd.Fallback.V2.readGroup limits checked index).mapError (liftGroupError .fallback) :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2.readGroup_unframed_agrees unframed

/-- The chosen strict wire witness covers the original frames and limits. -/
theorem readFrames_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2.readFrames_wire read

/-- Every accepted group is tied to its checked original leaf and chunk extents. -/
theorem readGroup_wire {parquet : Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2.readGroup_wire read

/-- Events retains the exact footer-ordered complete groups through EOS. -/
theorem readAll_success {name : String} {limits : Limits} {checked : Snappy.Checked name}
    {groups : List (List (Option Bytes))}
    (decoded : List.Forall₂ (fun index slots => readGroup limits checked index = .ok slots)
      (List.range checked.physical.snapshot.groupCount) groups) :
    readAll limits checked = .ok ⟨schema name,
      ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional), .eos⟩⟩ :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2.readAll_success decoded

/-- Events retains the complete prefix and first original typed group cause. -/
theorem readAll_first_error {name : String} {limits : Limits} {checked : Snappy.Checked name}
    {before after : List Nat} {index : Nat} {groups : List (List (Option Bytes))} {cause : GroupError}
    (split : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i slots => readGroup limits checked i = .ok slots) before groups)
    (failed : readGroup limits checked index = .error cause) :
    readAll limits checked = .ok ⟨schema name,
      ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional), .readError cause⟩⟩ :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2.readAll_first_error split earlier failed

/-- Native BinaryView retains the checked Events groups, opaque octets and EOS. -/
theorem convert_readback {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
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
        Stream.BatchesWire ipc view wire ⟨name, true, .binary⟩ ipc.batches start batches :=
  Proofs.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2.convert_readback written

/-- The first indexed source error precedes IPC admission. -/
theorem convert_first_error {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {checked : Snappy.Checked name} {before after : List Nat}
    {index : Nat} {earlier : List (List (Option Bytes))} {cause : GroupError}
    (opened : Snappy.openFile parquet.toPhysical input name = .ok checked)
    (indices : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (prefixRead : before.mapM (readGroup parquet checked) = .ok earlier)
    (failed : readGroup parquet checked index = .error cause) :
    convert parquet ipc view input name = .error (.column cause) := by
  simp [convert, opened, indices, List.mapM_append, prefixRead, List.mapM_cons, failed,
    Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2
