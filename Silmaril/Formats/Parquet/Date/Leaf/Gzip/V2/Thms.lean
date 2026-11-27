module

public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
public import Batteries.Data.List.Basic
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Thms
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip.V2.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip.V2.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2

open Silmaril.Relational

/-- The original V2 header fixes the slot counts, level extents and compression flag. -/
theorem planData_wire {bound : Bound} {frame : Page.Frame} {ordinal : Nat} {page : DataPage}
    (planned : planData bound frame ordinal = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 0 ∧
      page.params =
        ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
          ⟨0, if bound.field.layout == .required then 0 else 1⟩, header.numValues, Payload.Codec.gzip.id,
          header.encoding, .v2 header.numNulls header.numRows header.repetitionBytes
            header.definitionBytes (some header.isCompressed)⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.V2.planData_wire planned

/-- The V2 profile retains the same original frame chain, extent and footer count. -/
theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    GroupWire limits bound index checked (fun page => ∃ ordinal, planData bound page.frame ordinal = .ok page) :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.V2.checkGroup_wire accepted

/-- Success includes the original stored checksum check before V2 decoding. -/
theorem decodePage_wire {limits : Limits} {source : Bytes} {page : DataPage} {ordinal : Nat}
    {slots : Slots} (read : decodePage limits source page ordinal = .ok slots) :
    PageWire limits source page slots :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.V2.decodePage_wire read

/-- The original raw level prefix supplies the mask. Only the suffix has a codec,
with one exact GZIP member or the exact original PLAIN bytes. -/
theorem pageWire_exact {limits : Limits} {bound : Bound} {source : Bytes}
    {page : DataPage} {ordinal : Nat} {slots : Slots}
    (planned : planData bound page.frame ordinal = .ok page) (read : PageWire limits source page slots) :
    let stored := Page.Checksum.payloadBytes source page.frame
    ∃ (status : Page.Checksum.Status), ∃ header layout definitions encoded,
      ∃ (prepared : ScalarPage.Prepared), ∃ words,
      page.frame.value.kind = .dataV2 header ∧ header.encoding = 0 ∧
      source.slice? page.frame.payload.start (some page.frame.payload.stop) = some stored ∧
      stored.length = page.frame.value.compressedSize ∧ stored.length ≤ limits.scalar.compressedBytes ∧
      page.frame.value.uncompressedSize ≤ limits.scalar.uncompressedBytes ∧
      (match status with
       | .absent => page.frame.value.crc = none
       | .valid crc => page.frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
      header.repetitionBytes = 0 ∧ definitions.length = header.definitionBytes ∧
      stored.toList = definitions.toList ++ encoded ∧
      encoded.length = page.frame.value.compressedSize - header.definitionBytes ∧
      prepared.scalars.length = page.frame.value.uncompressedSize - header.definitionBytes ∧
      (if header.isCompressed then Compression.Gzip.decoder encoded = some (prepared.scalars.toList, [])
        else encoded = prepared.scalars.toList) ∧
      FlatPage.readMask layout header.numValues limits.scalar.levels definitions = .ok prepared.mask ∧
      ScalarPage.Kind.int32.readPlain (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words ∧
      slots.length = header.numValues ∧ header.numRows = header.numValues ∧
      (slots.filterMap id).length + header.numNulls = header.numValues :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.V2.pageWire_exact planned read

/-- Group slots concatenate the original V2 pages at the exact declared count. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧
      GroupWire limits bound index checked (fun page => ∃ ordinal, planData bound page.frame ordinal = .ok page) ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.V2.readGroup_wire read

/-- After planning, a page failure retains the original first indexed cause. -/
theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes page ordinal = .error cause) :
    readGroup limits bound index = .error cause :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.V2.readGroup_firstPageError admitted split earlier failed

/-- The complete earlier batches survive the original indexed source failure. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.V2.readAll_firstError opened split earlier failed

/-- The first source failure precedes IPC writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.V2.toIpc_firstError opened split earlier failed

/-- The actual Date32 stream preserves the descriptor and ordered nullable signed
slots through exact EOS at the original footer group boundaries. -/
theorem toIpc_readback {input : Snapshot.Limits} {limits : Limits} {output : Arrow.ObservationLimits}
    {ordinal : Nat} {bytes : Bytes} {wire : KBytes}
    (written : toIpc input limits output ordinal bytes = .ok wire) :
    ∃ bound groups, openLeaf input bytes ordinal = .ok bound ∧
      (List.range bound.snapshot.groupCount).mapM (readGroup limits bound) = .ok groups ∧
      groups.length = bound.snapshot.metadata.rowGroups.length ∧
      readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
        ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .eos⟩⟩ ∧
      ∃ result start, Arrow.DateStream.read output.ipc wire = .ok result ∧
        result = Arrow.DateStream.Writer.observation bound.binding.leaf.name bound.nullable groups ∧
        result.batches.length = groups.length ∧
        Arrow.DateStream.readSchema output.ipc wire = .ok (result.field, start) ∧
        Arrow.DateStream.BatchesWire output.ipc wire result.field output.ipc.batches start result.batches :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.V2.toIpc_readback written

/-- A stored checksum error takes precedence over splitting or expansion. -/
theorem decodePage_checksum_error {limits : Limits} {source : Bytes} {page : DataPage}
    {ordinal : Nat} {cause : Page.Checksum.Error}
    (failed : Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .error cause) :
    decodePage limits source page ordinal = .error (.gzip (atFrame ordinal page.frame (.checksum cause))) := by
  simp [decodePage, Gzip.decodePage_checksum_error failed, Except.mapError]

end Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2
