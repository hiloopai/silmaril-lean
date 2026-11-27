module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.Wire
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)
open Dictionary (DataPage CheckedChunk)

/-- A chosen dictionary tag occupies one nonempty prefix before all PLAIN pages. -/
theorem checkSequenceWith_wire {dictionaryTag : Int} {data : List DataPage}
    (checked : checkSequenceWith dictionaryTag data = .ok ()) : OrderedWith dictionaryTag data :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.checkSequenceWith_wire checked

/-- The admitted data frames have a nonempty RLE_DICTIONARY prefix
and a nonempty PLAIN suffix. -/
theorem checkSequence_wire {data : List DataPage} (checked : checkSequence data = .ok ()) :
    Ordered data :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.checkSequence_wire checked

theorem OrderedWith.tags {dictionaryTag : Int} {data : List DataPage} {page : DataPage}
    (ordered : OrderedWith dictionaryTag data) (member : page ∈ data) :
    page.params.encoding = dictionaryTag ∨ page.params.encoding = 0 := by
  obtain ⟨_, _, rfl, _, _, reference, plain⟩ := ordered
  exact (List.mem_append.mp member).imp (reference page) (plain page)

/-- The leading dictionary and both data segments use the original contiguous
frames and the original footer offsets and counts. -/
theorem checkGroup_wire {limits : Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {checked : CheckedChunk} (accepted : checkGroup limits leafLimits bound index = .ok checked) :
    selectChunkWith .dictionary leafLimits bound index = .ok checked.chunk ∧
      checked.chunk.span.stop - checked.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes checked.chunk.span = .ok checked.frames ∧
      Parquet.Page.Chain checked.chunk.span checked.chunk.span.start checked.chunk.span.stop checked.frames ∧
      checked.chunk.column.metadata.dictionaryPageOffset = some (checked.dictionary.header.start : Int) ∧
      checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some checked.chunk.column.metadata.dataPageOffset ∧
      Dictionary.readEntries limits bound checked.dictionary = .ok checked.entries ∧
      (∀ page ∈ checked.data, Dictionary.planDataWith admits bound page.frame = .ok page) ∧
      Ordered checked.data ∧
      (checked.data.map (·.params.numValues)).sum = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.checkGroup_wire accepted

theorem decodePage_wireWith {dictionaryTag : Int} {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {entries : Array Int64} {page : DataPage} {ordinal : Nat} {slots : List (Option Int64)}
    (admitted : page.params.encoding = dictionaryTag ∨ page.params.encoding = 0)
    (read : decodePage limits leafLimits bound entries page ordinal = .ok slots) :
    PageWireWith dictionaryTag limits leafLimits bound entries page slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.decodePage_wireWith admitted read

/-- The checked header selects the exact physical decoder for that payload. -/
theorem decodePage_wire {limits : Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {entries : Array Int64} {page : DataPage} {ordinal : Nat} {slots : List (Option Int64)}
    (admitted : admits page.params.encoding = true)
    (read : decodePage limits leafLimits bound entries page ordinal = .ok slots) :
    PageWire limits leafLimits bound entries page slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.decodePage_wire admitted read

/-- The group concatenates the two data segments in wire order, retaining the
selected descriptor and the declared number of nullable signed slots. -/
theorem readGroup_wire {limits : Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits leafLimits bound index = .ok checked ∧
      List.Forall₂ (PageWire limits leafLimits bound checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.length = checked.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.readGroup_wire read

/-- Once planning succeeds, the original error at the first failing
data page is returned after the preceding pages decode. -/
theorem readGroup_first_page_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {checked : CheckedChunk} {page : DataPage}
    {before after : List (DataPage × Nat)} {referencePages : List (List (Option Int64))} {cause : Leaf.Error}
    (admitted : checkGroup limits leafLimits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits leafLimits bound checked.entries.toArray item i) = .ok referencePages)
    (failed : decodePage limits leafLimits bound checked.entries.toArray page ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Fallback.readGroup_first_page_error admitted split earlier failed

/-- An error decoding the PLAIN suffix keeps its original payload cause,
wire ordinal and absolute header offset. -/
theorem decodePage_plain_error {limits : Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {entries : Array Int64} {page : DataPage} {ordinal : Nat}
    {cause : ScalarPage.Error} (plain : page.params.encoding = 0)
    (failed : ScalarPage.decode .int64 page.params leafLimits.page (Leaf.Internal.body bound page.frame) =
      .error cause) :
    decodePage limits leafLimits bound entries page ordinal =
      .error (.dictionaryPage ordinal page.frame.header.start (.plain cause)) := by
  simp [decodePage, plain, failed, Except.mapError, Dictionary.atFrame]

/-- The trace uses the same checked fallback reads in footer order. -/
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

end Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback
