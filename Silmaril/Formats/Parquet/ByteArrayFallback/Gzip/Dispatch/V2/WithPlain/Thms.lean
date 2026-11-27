module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain.Defs
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Thms
import Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain.Correctness

public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain

open Arrow.BinaryView
open Silmaril.Formats.Parquet.Plain.ByteArray

/-- Once the single framing pass succeeds, dispatch runs on exactly its original inputs. -/
theorem readGroup_framed {limits : Limits} {name : String}
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
      index checked.physical.binding.columnOrdinal name group.numRows.toNat frames :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain.readGroup_framed
    selected fits columnAt located framed

/-- Once original framing is available, the chosen strict reader has the exact same result,
including every typed failure. -/
theorem readGroup_agrees {limits : Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {frames : List Page.Frame} (original : Dispatch.FramedGroup limits checked index frames) :
    readGroup limits checked index =
      match profile frames with
      | .plain => Gzip.Plain.V2.readGroup limits checked index
      | .dictionary => Dictionary.V2.readGroup limits checked index
      | .fallback => Fallback.V2.readGroup limits checked index :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain.readGroup_agrees original

/-- A failure before original framing is available agrees with all three strict entry points. -/
theorem readGroup_unframed_agrees {limits : Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} (unframed : ∀ frames, ¬ Dispatch.FramedGroup limits checked index frames) :
    readGroup limits checked index = Gzip.Plain.V2.readGroup limits checked index ∧
      readGroup limits checked index = Dictionary.V2.readGroup limits checked index ∧
      readGroup limits checked index = Fallback.V2.readGroup limits checked index :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain.readGroup_unframed_agrees unframed

/-- The selected callback keeps its original frame and ordered slot relation. -/
theorem readFrames_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain.readFrames_wire read

/-- The original checked frames retain the byte limits and ordered slots of the chosen profile. -/
theorem readGroup_wire {parquet : Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain.readGroup_wire read

/-- The same checked unannotated binding gives exact opaque group slots through BinaryView EOS. -/
theorem convert_readback {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
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
        Stream.BatchesWire ipc view wire ⟨name, true, .binary⟩ ipc.batches start batches :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain.convert_readback written

/-- The first indexed source error precedes IPC admission. -/
theorem convert_first_error {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {checked : Snappy.Checked name} {before after : List Nat}
    {index : Nat} {earlier : List (List (Option Bytes))} {cause : Snappy.GroupError}
    (opened : Snappy.openFile parquet.toSnappyLimits input name = .ok checked)
    (indices : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (prefixRead : before.mapM (readGroup parquet checked) = .ok earlier)
    (failed : readGroup parquet checked index = .error cause) :
    convert parquet ipc view input name = .error (.column cause) :=
  Snappy.convertWith_first_error (readGroupAt := readGroup parquet) opened indices prefixRead failed

/-- A selected strict page failure retains its original coordinates ahead of IPC admission. -/
theorem convert_first_page_error {parquet : Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {checked : Snappy.Checked name} {before after : List Nat}
    {index column page offset : Nat} {earlier : List (List (Option Bytes))} {frames : List Page.Frame}
    {cause : FlatColumn.PageError Snappy.DecodeError}
    (opened : Snappy.openFile parquet.toSnappyLimits input name = .ok checked)
    (indices : List.range checked.physical.snapshot.groupCount = before ++ index :: after)
    (prefixRead : before.mapM (readGroup parquet checked) = .ok earlier)
    (original : Dispatch.FramedGroup parquet checked index frames)
    (failed : (match profile frames with
      | .plain => Gzip.Plain.V2.readGroup parquet checked index
      | .dictionary => Dictionary.V2.readGroup parquet checked index
      | .fallback => Fallback.V2.readGroup parquet checked index) =
        .error (.page index column name page offset cause)) :
    convert parquet ipc view input name = .error (.column (.page index column name page offset cause)) :=
  convert_first_error opened indices prefixRead ((readGroup_agrees original).trans failed)

end Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.WithPlain
