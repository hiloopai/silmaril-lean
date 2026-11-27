module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups.Classification
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)
open Dictionary (DataPage CheckedChunk)

/-- The actual codec and dictionary offset determine the only eligible planner. -/
theorem route_policy (metadata : Footer.ColumnMetadata) (selected : Option DictionaryCodec) :
    route metadata = .ok selected ↔
      match selected with
      | none => metadata.dictionaryPageOffset = none ∧ (metadata.codec = 0 ∨ metadata.codec = 1)
      | some codec => metadata.dictionaryPageOffset.isSome = true ∧ metadata.codec = codec.id :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups.route_policy metadata selected

/-- The selected layout has either only references or one ordered fallback transition. -/
theorem checkSequence_wire {data : List DataPage} (admitted : checkSequence data = .ok ()) :
    (dictionaryLayout data).Wire data :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups.checkSequence_wire admitted

/-- PLAIN parameters are derived from the original frames in their original order. -/
theorem planPlain_wire {limits : Leaf.Limits} {bound : Bound} {index : Nat} {chunk : Leaf.Chunk}
    {pages : List DataPage} (planned : planPlain limits bound index = .ok (.plain chunk pages)) :
    Leaf.selectChunk {limits with allowSnappy := true} bound index = .ok chunk ∧
      (chunk.column.metadata.codec = 0 ∨ chunk.column.metadata.codec = 1) ∧
      ∃ frames,
        Parquet.Page.readChunk limits.framing bound.snapshot.bytes chunk.span = .ok frames ∧
        Parquet.Page.Chain chunk.span chunk.span.start chunk.span.stop frames ∧
        (frames.map Leaf.Internal.pageSlots).sum = chunk.group.numRows.toNat ∧
        List.Forall₂ (fun frame page =>
          page.frame = frame ∧ Timestamp.Page.parameters bound.binding.leaf bound.levels
            chunk.column.metadata.codec frame.value = .ok page.params ∧ page.params.encoding = 0)
          frames pages :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups.planPlain_wire planned

/-- The leading dictionary and data pages keep their original absolute offsets.
The original codec and every page tag witness the selected layout. -/
theorem planDictionary_wire {codec : DictionaryCodec} {limits : Leaf.Dictionary.Limits}
    {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {layout : DictionaryLayout} {chunk : CheckedChunk}
    (planned : planDictionary codec limits leafLimits bound index = .ok (.dictionary codec layout chunk)) :
    Leaf.selectChunkWith codec.encoding leafLimits bound index = .ok chunk.chunk ∧
      chunk.chunk.column.metadata.codec = codec.id ∧
      chunk.chunk.span.stop - chunk.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes chunk.chunk.span = .ok chunk.frames ∧
      Parquet.Page.Chain chunk.chunk.span chunk.chunk.span.start chunk.chunk.span.stop chunk.frames ∧
      chunk.chunk.column.metadata.dictionaryPageOffset = some (chunk.dictionary.header.start : Int) ∧
      chunk.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some chunk.chunk.column.metadata.dataPageOffset ∧
      readEntries codec limits leafLimits bound chunk.dictionary = .ok chunk.entries ∧
      (∀ page ∈ chunk.data,
        Timestamp.Page.parameters bound.binding.leaf bound.levels codec.id page.frame.value = .ok page.params ∧
        Leaf.Fallback.admits page.params.encoding = true) ∧
      (chunk.data.map (·.params.numValues)).sum = chunk.chunk.group.numRows.toNat ∧
      layout.Wire chunk.data :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups.planDictionary_wire planned

/-- Dispatch reads the selected footer entry from the same bound snapshot. -/
theorem planGroup_route {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : Plan} (planned : planGroup limits leafLimits bound index = .ok plan) :
    ∃ group column selected, bound.snapshot.groupAt index = some group ∧
      group.columns[bound.ordinal - 1]? = some column ∧
      route column.metadata = .ok selected ∧
      match selected with
      | none => planPlain leafLimits bound index = .ok plan
      | some codec => planDictionary codec limits leafLimits bound index = .ok plan :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups.planGroup_route planned

/-- An unknown codec reports the original footer codec before decoding. -/
theorem planGroup_unknown_codec {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {group : Footer.RowGroup} {column : Footer.ColumnChunk}
    (found : bound.snapshot.groupAt index = some group)
    (selected : group.columns[bound.ordinal - 1]? = some column)
    (notPlain : column.metadata.codec ≠ 0) (notSnappy : column.metadata.codec ≠ 1) :
    planGroup limits leafLimits bound index = .error (.chunkCodec column.metadata.codec) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups.planGroup_unknown_codec found selected notPlain notSnappy

/-- Every successful read uses exactly its checked plan. -/
theorem readGroup_checked {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ plan, planGroup limits leafLimits bound index = .ok plan ∧
      decodePlan limits leafLimits bound plan = .ok slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups.readGroup_checked read

/-- After planning, a PLAIN page error retains the original decoder cause. -/
theorem readGroup_first_plain_page_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {chunk : Leaf.Chunk} {page : DataPage} {pages : List DataPage}
    {before after : List (DataPage × Nat)} {outputs : List (Slots bound)} {cause : Leaf.Error}
    (planned : planGroup limits leafLimits bound index = .ok (.plain chunk pages))
    (split : pages.zipIdx = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => Leaf.Internal.decodeFrame leafLimits.page bound
      chunk.column.metadata.codec item.frame i) = .ok outputs)
    (failed : Leaf.Internal.decodeFrame leafLimits.page bound chunk.column.metadata.codec page.frame ordinal =
      .error cause) :
    readGroup limits leafLimits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups.readGroup_first_plain_page_error planned split earlier failed

/-- After planning, a dictionary or fallback page error retains the original indexed decoder cause. -/
theorem readGroup_first_dictionary_page_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {codec : DictionaryCodec} {layout : DictionaryLayout}
    {chunk : CheckedChunk} {page : DataPage} {before after : List (DataPage × Nat)}
    {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (planned : planGroup limits leafLimits bound index = .ok (.dictionary codec layout chunk))
    (split : chunk.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodeDictionaryPage codec layout limits leafLimits bound chunk.entries.toArray item i) = .ok outputs)
    (failed : decodeDictionaryPage codec layout limits leafLimits bound chunk.entries.toArray page ordinal =
      .error cause) :
    readGroup limits leafLimits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups.readGroup_first_dictionary_page_error planned split earlier failed

/-- The trace uses the same checked group plans and reads in footer order. -/
theorem readBound_reference (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    let reference := Events.referenceGroupsWith (readGroup limits leafLimits bound)
      (List.range bound.snapshot.groupCount)
    readBound limits leafLimits bound = .ok ⟨Events.schema bound,
      ⟨reference.1.map (AlignedColumns.ofRows ∘ Events.rows bound), reference.2⟩⟩ :=
  Events.readBoundWith_reference bound (readGroup limits leafLimits bound)

/-- A group error retains precisely the earlier complete footer groups. -/
theorem readBound_first_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List (Slots bound)}
    {cause : Leaf.Error} (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits leafLimits bound) = .ok groups)
    (failed : readGroup limits leafLimits bound index = .error cause) :
    readBound limits leafLimits bound = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Events.readBoundWith_first_error split earlier failed

/-- The native Arrow stream reads back to the retained descriptor and the
ordered nullable counts of every complete footer group. -/
theorem convert_readback {profile : AnnotationProfile} {limits : Dictionary.Limits}
    {inputLimits : Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert profile limits inputLimits outputLimits input ordinal = .ok wire) :
    ∃ bound : Leaf.Bound, Events.ToIpc.openBoundWith profile inputLimits input ordinal = .ok bound ∧
      let reference := Events.referenceGroupsWith (readGroup limits inputLimits.leaf bound)
        (List.range bound.snapshot.groupCount)
      reference.2 = .eos ∧ ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = Events.ToIpc.selectedBinding bound ∧
        result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
          reference.1.map (List.map (Option.map Ticks.ticks)) :=
  Events.ToIpc.convertGroups_readback written

/-- The first failing footer group forwards the same cause before the IPC
writer attempts admission. -/
theorem convert_first_error {profile : AnnotationProfile} {limits : Dictionary.Limits}
    {inputLimits : Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (opened : Events.ToIpc.openBoundWith profile inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits inputLimits.leaf bound) = .ok groups)
    (failed : readGroup limits inputLimits.leaf bound index = .error cause) :
    convert profile limits inputLimits outputLimits input ordinal =
      .error (.source (.groupFailure index cause)) :=
  Events.ToIpc.convertGroups_first_error opened split earlier failed

end Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups
