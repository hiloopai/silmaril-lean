module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.V2.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.V2.Wire

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.V2

open Silmaril.Numeric.Timestamp (Ticks)

/-- The selected chunk retains its original frame chain, codec and checked count. -/
theorem checkGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat}
    {group : CheckedGroup} (checked : checkGroup limits leafLimits bound index = .ok group) :
    selectChunkWith .gzipPlainV2 leafLimits bound index = .ok group.chunk ∧
      group.chunk.column.metadata.codec = Payload.Codec.gzip.id ∧
      group.chunk.span.stop - group.chunk.span.start ≤ limits.dictionary.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes group.chunk.span = .ok group.frames ∧
      Parquet.Page.Chain group.chunk.span group.chunk.span.start group.chunk.span.stop group.frames ∧
      (group.frames.map Leaf.Internal.pageSlots).sum = group.chunk.group.numRows.toNat ∧
      group.chunk.column.metadata.dictionaryPageOffset = none ∧
      (group.chunk.span.start : Int) = group.chunk.column.metadata.dataPageOffset :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.V2.checkGroup_wire checked

/-- A successful PLAIN page preserves its checked original header and slot count. -/
theorem decodePage_wire {limits : ScalarPage.Limits} {bound : Bound} {frame : Parquet.Page.Frame}
    {ordinal : Nat} {slots : List (Option Int64)} (read : decodePage limits bound frame ordinal = .ok slots) :
    PageWire limits bound frame slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.V2.decodePage_wire read

/-- The raw definition prefix and flag-selected suffix reconstruct exact signed words. -/
theorem pageWire_decodes {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {frame : Parquet.Page.Frame} {slots : List (Option Int64)}
    (wire : PageWire (limits.withFuel leafLimits).page bound frame slots) :
    ∃ header layout definitions storedValues, ∃ prepared : ScalarPage.Prepared, ∃ words,
      frame.value.kind = .dataV2 header ∧ header.encoding = 0 ∧ header.numRows = header.numValues ∧
      Dictionary.Gzip.V2.BodyWire bound frame leafLimits.page header definitions storedValues prepared.scalars.toList ∧
      FlatPage.readMask layout header.numValues leafLimits.page.levels definitions = .ok prepared.mask ∧
      prepared.mask.count true = header.numValues - header.numNulls ∧
      Plain.decodeInt64 (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.V2.pageWire_decodes wire

/-- Every decoded page comes from its original frame, in the original order. -/
theorem readGroup_wire {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ group pages, checkGroup limits leafLimits bound index = .ok group ∧
      List.Forall₂ (PageWire (limits.withFuel leafLimits).page bound) group.frames pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = group.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.V2.readGroup_wire read

/-- After framing and count admission, preserve the first original page failure. -/
theorem readGroup_first_page_error {limits : Limits} {leafLimits : Leaf.Limits} {bound : Bound} {index ordinal : Nat}
    {group : CheckedGroup} {frame : Parquet.Page.Frame} {before after : List (Parquet.Page.Frame × Nat)}
    {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (checked : checkGroup limits leafLimits bound index = .ok group)
    (split : group.frames.zipIdx = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => decodePage (limits.withFuel leafLimits).page bound item i) = .ok outputs)
    (failed : decodePage (limits.withFuel leafLimits).page bound frame ordinal = .error cause) :
    readGroup limits leafLimits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.Gzip.V2.readGroup_first_page_error checked split earlier failed

end Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.V2
