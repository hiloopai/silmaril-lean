module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- A PLAIN V1 header is the exact condition for a fallback choice. -/
theorem profile_fallback_iff {frames : List Parquet.Page.Frame} :
    profile frames = .fallback ↔
      ∃ frame ∈ frames, ∃ header, frame.value.kind = .dataV1 header ∧ header.encoding = 0 :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.profile_fallback_iff

/-- The choice comes from the original selected frames in their checked chunk order. -/
theorem planGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : Plan} (planned : planGroup limits leafLimits bound index = .ok plan) :
    selectChunkWith .gzipDictionaryV1 leafLimits bound index = .ok plan.framed.chunk ∧
      plan.framed.chunk.span.stop - plan.framed.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes plan.framed.chunk.span = .ok plan.framed.frames ∧
      Parquet.Page.Chain plan.framed.chunk.span plan.framed.chunk.span.start plan.framed.chunk.span.stop
        plan.framed.frames ∧
      plan.framed.chunk.column.metadata.dictionaryPageOffset = some (plan.framed.dictionary.header.start : Int) ∧
      plan.framed.chunk.column.metadata.dataPageOffset = (plan.framed.firstData.header.start : Int) ∧
      (plan.choice = .fallback ↔ ∃ frame ∈ plan.framed.data, ∃ header,
        frame.value.kind = .dataV1 header ∧ header.encoding = 0) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.planGroup_wire planned

/-- The chosen branch returns the exact standalone result, including any typed error. -/
theorem readGroup_matches {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : Plan} (planned : planGroup limits leafLimits bound index = .ok plan) :
    readGroup limits leafLimits bound index =
      match plan.choice with
      | .dictionary => Leaf.Dictionary.Gzip.readGroup limits leafLimits bound index
      | .fallback => Leaf.Fallback.Gzip.readGroup limits leafLimits bound index :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.readGroup_matches planned

/-- A shared framing failure keeps the same cause in either standalone profile and dispatch. -/
theorem framing_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {cause : Leaf.Error}
    (failed : Leaf.Dictionary.frameGroupUsing .gzipDictionaryV1 limits.dictionary leafLimits bound index = .error cause) :
    readGroup limits leafLimits bound index = .error cause ∧
      Leaf.Dictionary.Gzip.readGroup limits leafLimits bound index = .error cause ∧
      Leaf.Fallback.Gzip.readGroup limits leafLimits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.framing_error failed

/-- Successful dispatch retains the original frames, chosen physical wire evidence and signed slots. -/
theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : Plan} {slots : Slots bound}
    (planned : planGroup limits leafLimits bound index = .ok plan)
    (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages,
      (match plan.choice with
       | .dictionary => Leaf.Dictionary.Gzip.checkGroup limits leafLimits bound index
       | .fallback => Leaf.Fallback.Gzip.checkGroup limits leafLimits bound index) = .ok checked ∧
      checked.frames = plan.framed.frames ∧
      Leaf.Dictionary.Gzip.readEntries limits leafLimits bound checked.dictionary = .ok checked.entries ∧
      List.Forall₂ (fun page raw =>
        match plan.choice with
        | .dictionary => Leaf.Dictionary.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
            bound checked.entries.toArray page raw
        | .fallback => Leaf.Fallback.Snappy.DataWire limits.dictionary (limits.withFuel leafLimits)
            bound checked.entries.toArray page raw) checked.data pages ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.readGroup_wire planned read

/-- The event trace retains precisely the complete groups preceding the failure. -/
theorem readBound_first_error {limits : Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List (Slots bound)}
    {cause : Leaf.Error} (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    readBound limits leafLimits bound = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Events.readBoundWith_first_error split earlier failed

/-- Complete native IPC reads back through EOS with the same descriptor and
ordered nullable signed ticks from the original footer groups. -/
theorem convert_readback {limits : Limits} {inputLimits : Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert limits inputLimits outputLimits input ordinal = .ok wire) :
    ∃ bound : Bound, Events.ToIpc.openBound inputLimits input ordinal = .ok bound ∧
      let reference := Events.referenceGroupsWith (readGroup limits inputLimits.leaf bound)
        (List.range bound.snapshot.groupCount)
      reference.2 = .eos ∧ ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = Events.ToIpc.selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          reference.1.map (List.map (Option.map Ticks.ticks)) :=
  Events.ToIpc.convertGroups_readback written

/-- The first failed original group is reported before writer admission. -/
theorem convert_first_error {limits : Limits} {inputLimits : Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (opened : Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits outputLimits input ordinal =
      .error (.source (.groupFailure index cause)) :=
  Events.ToIpc.convertGroups_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1
