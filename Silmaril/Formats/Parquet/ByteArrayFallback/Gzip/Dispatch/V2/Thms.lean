module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.Defs
import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Thms
import Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.Correctness

public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2

open Arrow.BinaryView
open Plain.ByteArray

/-- Once original framing is available, the chosen strict reader has the exact same result,
including every typed failure. -/
theorem readGroup_agrees {limits : Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {frames : List Page.Frame} (original : Dispatch.FramedGroup limits checked index frames) :
    readGroup limits checked index =
      match profile frames with
      | .dictionary => Dictionary.V2.readGroup limits checked index
      | .fallback => Fallback.V2.readGroup limits checked index :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.readGroup_agrees original

/-- A failure before original framing is available agrees with both strict entry points. -/
theorem readGroup_unframed_agrees {limits : Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} (unframed : ∀ frames, ¬ Dispatch.FramedGroup limits checked index frames) :
    readGroup limits checked index = Dictionary.V2.readGroup limits checked index ∧
      readGroup limits checked index = Fallback.V2.readGroup limits checked index :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.readGroup_unframed_agrees unframed

/-- The selected callback keeps its original frame and ordered slot relation. -/
theorem readFrames_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.readFrames_wire read

/-- The original checked frames retain the byte limits and ordered slots of the chosen profile. -/
theorem readGroup_wire {parquet : Limits} {name : String} {checked : Snappy.Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.readGroup_wire read

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
  Proofs.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2.convert_readback written

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

end Silmaril.Formats.Parquet.ByteArrayFallback.Gzip.Dispatch.V2
