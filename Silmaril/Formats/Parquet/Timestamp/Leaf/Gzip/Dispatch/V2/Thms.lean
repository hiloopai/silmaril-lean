module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- A PLAIN V2 header is the exact condition for a fallback choice. -/
theorem dictionaryProfile_fallback_iff {frames : List Parquet.Page.Frame} :
    dictionaryProfile frames = .fallback ↔
      ∃ frame ∈ frames, ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 0 :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.dictionaryProfile_fallback_iff

/-- The choice comes from the original selected frames in their checked chunk order. -/
theorem planDictionary_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} (planned : planDictionary limits leafLimits bound index = .ok plan) :
    selectChunkWith .gzipDictionaryV2 leafLimits bound index = .ok plan.framed.chunk ∧
      plan.framed.chunk.span.stop - plan.framed.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes plan.framed.chunk.span = .ok plan.framed.frames ∧
      Parquet.Page.Chain plan.framed.chunk.span plan.framed.chunk.span.start plan.framed.chunk.span.stop
        plan.framed.frames ∧
      plan.framed.chunk.column.metadata.dictionaryPageOffset = some (plan.framed.dictionary.header.start : Int) ∧
      plan.framed.chunk.column.metadata.dataPageOffset = (plan.framed.firstData.header.start : Int) ∧
      (plan.profile = .fallback ↔ ∃ frame ∈ plan.framed.data, ∃ header,
        frame.value.kind = .dataV2 header ∧ header.encoding = 0) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.planDictionary_wire planned

/-- The chosen branch returns the exact standalone result, including any typed error. -/
theorem readDictionary_matches {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} (planned : planDictionary limits leafLimits bound index = .ok plan) :
    readDictionary limits leafLimits bound index =
      match plan.profile with
      | .references => Leaf.Dictionary.Gzip.V2.readGroup limits leafLimits bound index
      | .fallback => Leaf.Fallback.Gzip.V2.readGroup limits leafLimits bound index :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.readDictionary_matches planned

/-- A shared framing failure keeps the same cause in either standalone profile and dispatch. -/
theorem dictionary_framing_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {cause : Leaf.Error}
    (failed : Leaf.Dictionary.frameGroupUsing .gzipDictionaryV2 limits.dictionary leafLimits bound index = .error cause) :
    readDictionary limits leafLimits bound index = .error cause ∧
      Leaf.Dictionary.Gzip.V2.readGroup limits leafLimits bound index = .error cause ∧
      Leaf.Fallback.Gzip.V2.readGroup limits leafLimits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.dictionary_framing_error failed

/-- Successful dispatch retains the original frames, chosen physical wire evidence and signed slots. -/
theorem readDictionary_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} {slots : Slots bound}
    (planned : planDictionary limits leafLimits bound index = .ok plan)
    (read : readDictionary limits leafLimits bound index = .ok slots) :
    DictionaryWire limits leafLimits bound index plan slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.readDictionary_wire planned read

/-- Routing uses the dictionary offset of the exact selected footer column. -/
theorem hasDictionary_selected {encoding : Leaf.ChunkEncoding} {limits : Leaf.Limits} {bound : Bound}
    {index : Nat} {chunk : Leaf.Chunk} (selected : selectChunkWith encoding limits bound index = .ok chunk) :
    hasDictionary bound index = .ok chunk.column.metadata.dictionaryPageOffset.isSome :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.hasDictionary_selected selected

/-- An original group or column lookup error is forwarded unchanged. -/
theorem readGroup_route_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {cause : Leaf.Error} (failed : hasDictionary bound index = .error cause) :
    readGroup limits leafLimits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.readGroup_route_error failed

/-- The PLAIN route preserves the dedicated reader's complete result. -/
theorem readGroup_plain_matches {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (routed : hasDictionary bound index = .ok false) :
    readGroup limits leafLimits bound index = Gzip.V2.readGroup limits leafLimits bound index :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.readGroup_plain_matches routed

/-- Both dictionary-backed branches preserve the dedicated result, including typed errors. -/
theorem readGroup_dictionary_matches {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} (routed : hasDictionary bound index = .ok true)
    (planned : planDictionary limits leafLimits bound index = .ok plan) :
    readGroup limits leafLimits bound index =
      match plan.profile with
      | .references => Dictionary.Gzip.V2.readGroup limits leafLimits bound index
      | .fallback => Fallback.Gzip.V2.readGroup limits leafLimits bound index :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.readGroup_dictionary_matches routed planned

/-- Every completed group has the chosen reader's original wire witness. -/
theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    GroupWire limits leafLimits bound index slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.readGroup_wire read

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

end Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2
