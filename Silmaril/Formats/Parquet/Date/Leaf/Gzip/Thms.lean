module

public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip.Wire
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip.Events

public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Gzip

open Silmaril.Relational

/-- The original V1 header supplies the exact PLAIN scalar parameters. -/
theorem planData_wire {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV1 header ∧ header.encoding = 0 ∧
      page.params =
        ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
          ⟨0, if bound.field.layout == .required then 0 else 1⟩, header.numValues, Payload.Codec.gzip.id,
          header.encoding, .v1 header.definitionLevelEncoding header.repetitionLevelEncoding⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.planData_wire planned

/-- A profile that retains its original page frames shares the checked GZIP chunk. -/
theorem checkGroupWith_wire {ε : Type} {wrap : GroupError → ε}
    {plan : Page.Frame → Nat → Except ε DataPage} {valid : DataPage → Prop}
    {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (keeps : ∀ {frame ordinal page}, plan frame ordinal = .ok page → page.frame = frame ∧ valid page)
    (accepted : checkGroupWith wrap plan limits bound index = .ok checked) :
    GroupWire limits bound index checked valid :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.checkGroupWith_wire keeps accepted

/-- The selected footer range supplies the original bounded frames and slot total. -/
theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    GroupWire limits bound index checked :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.checkGroup_wire accepted

/-- The original stored CRC is checked before physical decode. -/
theorem decodePage_wire {limits : Limits} {source : Bytes} {page : DataPage} {ordinal : Nat}
    {slots : Slots} (read : decodePage limits source page ordinal = .ok slots) :
    PageWire limits source page slots :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.decodePage_wire read

/-- A checked CRC status identifies the exact bounded stored slice. -/
theorem stored_exact {cap : Nat} {source : Bytes} {frame : Page.Frame} {status : Page.Checksum.Status}
    (verified : Page.Checksum.verify cap source frame = .ok status) :
    let stored := Page.Checksum.payloadBytes source frame
    source.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧ stored.length ≤ cap ∧
      match status with
      | .absent => frame.value.crc = none
      | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.stored_exact verified

/-- Scalar admission independently bounds the expanded page size. -/
theorem expanded_bound {params : ScalarPage.Parameters} {limits : ScalarPage.Limits}
    {source : Bytes} {layout : FlatPage.Layout}
    (valid : ScalarPage.validate params limits source = .ok layout) :
    params.sizes.uncompressed ≤ limits.uncompressedBytes :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.expanded_bound valid

/-- The exact bounded stored bytes expand as one GZIP member into the checked
V1 level and signed PLAIN slices, with independent stored and expanded caps. -/
theorem pageWire_exact {limits : Limits} {bound : Bound} {source : Bytes} {page : DataPage}
    {slots : Slots} (planned : planData bound page.frame = .ok page)
    (read : PageWire limits source page slots) :
    let stored := Page.Checksum.payloadBytes source page.frame
    ∃ (status : Page.Checksum.Status), ∃ layout expanded prepared words,
      source.slice? page.frame.payload.start (some page.frame.payload.stop) = some stored ∧
      stored.length = page.frame.value.compressedSize ∧ stored.length ≤ limits.scalar.compressedBytes ∧
      (match status with
       | .absent => page.frame.value.crc = none
       | .valid crc => page.frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
      Compression.Gzip.decoder stored.toList = some (expanded, []) ∧
      expanded.length = page.frame.value.uncompressedSize ∧ expanded.length ≤ limits.scalar.uncompressedBytes ∧
      ScalarPage.PreparedWire page.params limits.scalar layout stored prepared ∧
      ScalarPage.Kind.int32.readPlain (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words ∧ slots.length = page.params.numValues :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.pageWire_exact planned read

/-- Group slots concatenate the original pages in order at the declared row count. -/
theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.readGroup_wire read

/-- After planning, the original first failed page retains its error. -/
theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes page ordinal = .error cause) :
    readGroup limits bound index = .error cause :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.readGroup_firstPageError admitted split earlier failed

/-- A late failure retains the earlier complete batches and original indexed cause. -/
theorem readAll_firstError {input : Snapshot.Limits} {limits : Limits} {ordinal : Nat} {bytes : Bytes}
    {bound : Bound} {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    readAll input limits ordinal bytes = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.readAll_firstError opened split earlier failed

/-- Source errors take precedence over writer checks. -/
theorem toIpc_firstError {input : Snapshot.Limits} {limits : Limits}
    {output : Arrow.ObservationLimits} {ordinal : Nat} {bytes : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List Slots} {cause : GroupError}
    (opened : openLeaf input bytes ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup limits bound) = .ok groups)
    (failed : readGroup limits bound index = .error cause) :
    toIpc input limits output ordinal bytes = .error (.source (.groupFailure index cause)) :=
  Proofs.Formats.Parquet.Date.Leaf.Gzip.toIpc_firstError opened split earlier failed

/-- Native Date32 IPC preserves the exact descriptor, signed nullable slots,
and one batch per original footer group through exact EOS. -/
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
  Proofs.Formats.Parquet.Date.Leaf.Gzip.toIpc_readback written

/-- The original CRC failure prevents scalar or GZIP decoding. -/
theorem decodePage_checksum_error {limits : Limits} {source : Bytes} {page : DataPage}
    {ordinal : Nat} {cause : Page.Checksum.Error}
    (failed : Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .error cause) :
    decodePage limits source page ordinal = .error (atFrame ordinal page.frame (.checksum cause)) := by
  simp [decodePage, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Date.Leaf.Gzip
