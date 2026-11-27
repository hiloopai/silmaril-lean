module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

/-- A PLAIN V2 header is the exact condition for choosing the fallback branch. -/
theorem dictionaryProfile_fallback_iff {frames : List Parquet.Page.Frame} :
    dictionaryProfile frames = .fallback ↔
      ∃ frame ∈ frames, ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 0 :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.dictionaryProfile_fallback_iff

/-- The selected original frame chain and footer offsets determine the branch. -/
theorem planDictionary_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} (planned : planDictionary limits leafLimits bound index = .ok plan) :
    selectChunkWith .zstdDictionaryV2 leafLimits bound index = .ok plan.framed.chunk ∧
      plan.framed.chunk.column.metadata.codec = Payload.Codec.zstd.id ∧
      plan.framed.chunk.span.stop - plan.framed.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes plan.framed.chunk.span = .ok plan.framed.frames ∧
      Parquet.Page.Chain plan.framed.chunk.span plan.framed.chunk.span.start plan.framed.chunk.span.stop
        plan.framed.frames ∧
      plan.framed.chunk.column.metadata.dictionaryPageOffset = some (plan.framed.dictionary.header.start : Int) ∧
      plan.framed.chunk.column.metadata.dataPageOffset = (plan.framed.firstData.header.start : Int) ∧
      (plan.profile = .fallback ↔ ∃ frame ∈ plan.framed.data, ∃ header,
        frame.value.kind = .dataV2 header ∧ header.encoding = 0) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.planDictionary_wire planned

/-- The chosen plan returns the complete strict result, including typed errors. -/
theorem readDictionary_matches {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} (planned : planDictionary limits leafLimits bound index = .ok plan) :
    readDictionary limits leafLimits bound index =
      match plan.profile with
      | .references => Leaf.Dictionary.Zstd.V2.readGroup limits leafLimits bound index
      | .fallback => Leaf.Fallback.Zstd.V2.readGroup limits leafLimits bound index :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.readDictionary_matches planned

/-- Both dictionary-backed profiles share the original framing failure. -/
theorem dictionary_framing_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {cause : Leaf.Error}
    (failed : Leaf.Dictionary.frameGroupUsing .zstdDictionaryV2 limits.dictionary leafLimits bound index = .error cause) :
    readDictionary limits leafLimits bound index = .error (.selection cause) ∧
      Leaf.Dictionary.Zstd.V2.readGroup limits leafLimits bound index = .error (.selection cause) ∧
      Leaf.Fallback.Zstd.V2.readGroup limits leafLimits bound index = .error (.selection cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.dictionary_framing_error failed

/-- The completed dictionary-backed branch retains original frames, bounds and payload witnesses. -/
theorem readDictionary_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} {slots : Slots bound}
    (planned : planDictionary limits leafLimits bound index = .ok plan)
    (read : readDictionary limits leafLimits bound index = .ok slots) :
    DictionaryWire limits leafLimits bound index plan slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.readDictionary_wire planned read

/-- Routing uses the dictionary offset of the exact selected footer column. -/
theorem hasDictionary_selected {encoding : Leaf.ChunkEncoding} {limits : Leaf.Limits} {bound : Bound}
    {index : Nat} {chunk : Leaf.Chunk} (selected : selectChunkWith encoding limits bound index = .ok chunk) :
    hasDictionary bound index = .ok chunk.column.metadata.dictionaryPageOffset.isSome :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.hasDictionary_selected selected

/-- An original group or column lookup error is retained. -/
theorem readGroup_route_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {cause : Leaf.Error} (failed : hasDictionary bound index = .error cause) :
    readGroup limits leafLimits bound index = .error (.selection cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.readGroup_route_error failed

/-- The PLAIN route agrees with the standalone PLAIN reader. -/
theorem readGroup_plain_matches {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    (routed : hasDictionary bound index = .ok false) :
    readGroup limits leafLimits bound index = Leaf.Zstd.V2.readGroup (Leaf.Dictionary.Zstd.V2.scalarLimits limits) leafLimits bound index :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.readGroup_plain_matches routed

/-- The selected dictionary-backed route agrees with the standalone reader. -/
theorem readGroup_dictionary_matches {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : DictionaryPlan} (routed : hasDictionary bound index = .ok true)
    (planned : planDictionary limits leafLimits bound index = .ok plan) :
    readGroup limits leafLimits bound index =
      match plan.profile with
      | .references => Leaf.Dictionary.Zstd.V2.readGroup limits leafLimits bound index
      | .fallback => Leaf.Fallback.Zstd.V2.readGroup limits leafLimits bound index :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.readGroup_dictionary_matches routed planned

/-- Dictionary framing errors keep the original source cause in dispatch. -/
theorem readGroup_dictionary_framing_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {cause : Leaf.Error} (routed : hasDictionary bound index = .ok true)
    (failed : Leaf.Dictionary.frameGroupUsing .zstdDictionaryV2 limits.dictionary leafLimits bound index = .error cause) :
    readGroup limits leafLimits bound index = .error (.selection cause) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.readGroup_dictionary_framing_error routed failed

/-- Every completed group retains the chosen strict reader's wire evidence. -/
theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    GroupWire limits leafLimits bound index slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.readGroup_wire read

/-- The first source group error retains the complete earlier event batches. -/
theorem readBound_first_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : GroupError}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    readBound limits leafLimits bound = .ok ⟨Leaf.Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Leaf.Zstd.V2.readBoundWith_first_error (read := readGroup limits leafLimits bound) split earlier failed

/-- The original typed source failure precedes IPC writer admission. -/
theorem convert_first_error {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : GroupError}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert limits inputLimits output input ordinal = .error (.source (.groupFailure index cause)) :=
  Leaf.Zstd.V2.convertWith_first_error (read := readGroup limits inputLimits.leaf) opened split earlier failed

/-- Native IPC preserves the bound descriptor and original ordered signed slots through EOS. -/
theorem convert_readback {limits : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {output : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert limits inputLimits output input ordinal = .ok wire) :
    ∃ bound groups, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (readGroup limits inputLimits.leaf bound) = .ok groups ∧
      readBound limits inputLimits.leaf bound = .ok ⟨Leaf.Events.schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ Leaf.Events.rows bound), .eos⟩⟩ ∧
      ∃ result, Arrow.TimestampStream.read output.ipc wire = .ok result ∧
        result.binding = Leaf.Events.ToIpc.selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          groups.map (List.map (Option.map Ticks.ticks)) :=
  Leaf.Zstd.V2.convertWith_readback (read := readGroup limits inputLimits.leaf) written

end Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2
