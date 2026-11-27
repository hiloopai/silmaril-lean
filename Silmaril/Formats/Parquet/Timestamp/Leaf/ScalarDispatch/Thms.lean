module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.V2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Defs
public import Mathlib.Data.List.Forall2
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Wire
import Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Compressed
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms

public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)


/-- The checked group covers the original selected chunk, with its complete frame chain and row count. -/
theorem checkGroup_wire {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {group : CheckedGroup} (checked : checkGroup limits bound index = .ok group) :
    Leaf.selectChunkWith .scalarDispatch limits bound index = .ok group.chunk ∧
      bound.snapshot.groupAt index = some group.chunk.group ∧
      group.chunk.group.columns[bound.ordinal - 1]? = some group.chunk.column ∧
      (group.chunk.column.metadata.codec = 0 ∨ group.chunk.column.metadata.codec = 1 ∨
        group.chunk.column.metadata.codec = 2 ∨ group.chunk.column.metadata.codec = 6) ∧
      group.chunk.column.metadata.dictionaryPageOffset = none ∧
      (group.chunk.span.start : Int) = group.chunk.column.metadata.dataPageOffset ∧
      (group.chunk.span.stop : Int) =
        group.chunk.column.metadata.dataPageOffset + group.chunk.column.metadata.totalCompressedSize ∧
      Parquet.Page.readChunk limits.framing bound.snapshot.bytes group.chunk.span = .ok group.frames ∧
      Parquet.Page.Chain group.chunk.span group.chunk.span.start group.chunk.span.stop group.frames ∧
      (group.frames.map Leaf.Internal.pageSlots).sum = group.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.checkGroup_wire checked

/-- A successful route has exactly the original header tag and an original footer declaration. -/
theorem route_ok_iff {declared : List Int} {frame : Parquet.Page.Frame} {ordinal : Nat} {encoding : Encoding} :
    route declared frame ordinal = .ok encoding ↔
      pageTag frame = some encoding.tag ∧ encoding.tag ∈ declared :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.route_ok_iff

/-- Every successful branch retains its own original CRC, prepared bytes, and physical slot evidence. -/
theorem decodePage_wire {scalars : Limits} {limits : ScalarPage.Limits}
    {bound : Bound} {codec : Int} {declared : List Int} {frame : Parquet.Page.Frame} {ordinal : Nat}
    {slots : List (Option Int64)} (read : decodePage scalars limits bound codec declared frame ordinal = .ok slots) :
    PageWire scalars limits bound codec declared frame slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.decodePage_wire read

/-- Selection and decoding retain original frame order and the exact signed, nullable slots. -/
theorem readGroup_wire {scalars : Limits} {limits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readGroup scalars limits bound index = .ok slots) :
    ∃ group pages, checkGroup limits bound index = .ok group ∧
      List.Forall₂ (PageWire scalars limits.page bound group.chunk.column.metadata.codec
        group.chunk.column.metadata.encodings) group.frames pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = group.chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.readGroup_wire read

/-- After framing and row-count admission, the first failing original page supplies its exact cause. -/
theorem readGroup_first_page_error {scalars : Limits} {limits : Leaf.Limits} {bound : Bound} {index ordinal : Nat}
    {group : CheckedGroup} {frame : Parquet.Page.Frame} {before after : List (Parquet.Page.Frame × Nat)}
    {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (checked : checkGroup limits bound index = .ok group)
    (split : group.frames.zipIdx = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => decodePage scalars limits.page bound group.chunk.column.metadata.codec group.chunk.column.metadata.encodings item i) = .ok outputs)
    (failed : decodePage scalars limits.page bound group.chunk.column.metadata.codec group.chunk.column.metadata.encodings frame ordinal = .error cause) :
    readGroup scalars limits bound index = .error cause :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.readGroup_first_page_error checked split earlier failed

/-- A successful standalone delta group produces exactly the same slots. -/
theorem readGroup_agrees_delta {scalars : Limits} {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {slots : Slots bound} (accepted : Leaf.Delta.readGroup scalars.delta limits bound index = .ok slots) :
    readGroup scalars limits bound index = .ok slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.readGroup_agrees_delta accepted

/-- A successful standalone byte-stream-split group produces exactly the same slots. -/
theorem readGroup_agrees_split {scalars : Limits} {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {slots : Slots bound} (accepted : Leaf.ByteStreamSplit.readGroup scalars.split limits bound index = .ok slots) :
    readGroup scalars limits bound index = .ok slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.readGroup_agrees_split accepted

/-- A successful standalone PLAIN group agrees whenever its footer declares PLAIN. -/
theorem readGroup_agrees_plain {scalars : Limits} {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {slots : Slots bound}
    (advertised : ∀ chunk, Leaf.selectChunk limits bound index = .ok chunk → 0 ∈ chunk.column.metadata.encodings)
    (accepted : Leaf.readGroup limits bound index = .ok slots) :
    readGroup scalars limits bound index = .ok slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.readGroup_agrees_plain advertised accepted

/-- The checksummed uncompressed PLAIN V2 reader agrees on successful, declared PLAIN groups. -/
theorem readGroup_agrees_plain_v2_uncompressed {scalars : Limits} {limits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound}
    (advertised : ∀ chunk, Leaf.selectChunk {limits with allowSnappy := false} bound index = .ok chunk →
      0 ∈ chunk.column.metadata.encodings)
    (accepted : Leaf.Uncompressed.V2.readGroup limits bound index = .ok slots) :
    readGroup scalars limits bound index = .ok slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.readGroup_agrees_plain_v2_uncompressed advertised accepted

/-- The checksummed Snappy PLAIN V2 reader agrees on successful, declared PLAIN groups. -/
theorem readGroup_agrees_plain_v2_snappy {scalars : Limits} {limits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound}
    (advertised : ∀ chunk, Leaf.selectChunk {limits with allowSnappy := true} bound index = .ok chunk →
      0 ∈ chunk.column.metadata.encodings)
    (accepted : Leaf.SnappyV2.readGroup limits bound index = .ok slots) :
    readGroup scalars limits bound index = .ok slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.readGroup_agrees_plain_v2_snappy advertised accepted

/-- Composing successful group agreement over the checked source preserves the emitted IPC bytes. -/
theorem convert_agrees {scalars : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    {strict : (bound : Bound) → Nat → Except Leaf.Error (Slots bound)}
    (compatible : ∀ bound, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound →
      ∀ index slots, strict bound index = .ok slots → readGroup scalars inputLimits.leaf bound index = .ok slots)
    (written : Leaf.Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal strict = .ok wire) :
    convert scalars inputLimits outputLimits input ordinal = .ok wire :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.convert_agrees compatible written

/-- Native Arrow IPC preserves the original descriptor and exact footer-order group ticks through EOS. -/
theorem convert_readback {scalars : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    (written : convert scalars inputLimits outputLimits input ordinal = .ok wire) :
    ∃ bound : Bound, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound ∧
      ∃ result, Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧
        result.binding = Leaf.Events.ToIpc.selectedBinding bound ∧
        List.Forall₂ (fun index counts =>
          ∃ slots, readGroup scalars inputLimits.leaf bound index = .ok slots ∧
            counts = slots.map (Option.map Ticks.ticks))
          (List.range bound.snapshot.groupCount)
          (result.batches.map Arrow.TimestampBatch.Writer.tickCounts) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.convert_readback written

/-- The selected decoder supplies the entire result, including its unchanged typed failure. -/
theorem decodePage_branch {scalars : Limits} {limits : ScalarPage.Limits} {bound : Bound}
    {codec : Int} {declared : List Int} {frame : Parquet.Page.Frame} {ordinal : Nat} {encoding : Encoding}
    (chosen : route declared frame ordinal = .ok encoding) :
    decodePage scalars limits bound codec declared frame ordinal =
      decodeSelected scalars limits bound codec encoding frame ordinal := by
  simp [decodePage, chosen, Bind.bind, Except.bind]

/-- An unsupported or undeclared original page fails before body decoding. -/
theorem decodePage_route_error {scalars : Limits} {limits : ScalarPage.Limits} {bound : Bound}
    {codec : Int} {declared : List Int} {frame : Parquet.Page.Frame} {ordinal : Nat} {cause : Leaf.Error}
    (failed : route declared frame ordinal = .error cause) :
    decodePage scalars limits bound codec declared frame ordinal = .error cause := by
  simp [decodePage, failed, Bind.bind, Except.bind]

/-- A failed footer group retains exactly the earlier complete batches. -/
theorem readBound_first_error {scalars : Limits} {limits : Leaf.Limits} {bound : Bound}
    {before after : List Nat} {index : Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup scalars limits bound) = .ok groups)
    (failed : readGroup scalars limits bound index = .error cause) :
    readBound scalars limits bound = .ok ⟨Events.schema bound,
      ⟨groups.map (AlignedColumns.ofRows ∘ Events.rows bound), .readError (.groupFailure index cause)⟩⟩ :=
  Events.readBoundWith_first_error split earlier failed

/-- An original source failure preempts native writer admission. -/
theorem convert_first_error {scalars : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {ordinal index : Nat} {bound : Bound}
    {before after : List Nat} {groups : List (Slots bound)} {cause : Leaf.Error}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (readGroup scalars inputLimits.leaf bound) = .ok groups)
    (failed : readGroup scalars inputLimits.leaf bound index = .error cause) :
    convert scalars inputLimits outputLimits input ordinal = .error (.source (.groupFailure index cause)) :=
  Events.ToIpc.convertGroups_first_error opened split earlier failed


/-- The checked footer admits only the declared scalar union and optional RLE, with absent dictionary and index offsets. -/
theorem checkGroup_encodings {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {group : CheckedGroup} (checked : checkGroup limits bound index = .ok group) :
    let metadata := group.chunk.column.metadata
    metadata.indexPageOffset = none ∧ metadata.dictionaryPageOffset = none ∧
      (∀ tag ∈ metadata.encodings, tag = 0 ∨ tag = 3 ∨ tag = 5 ∨ tag = 9) ∧
      (0 ∈ metadata.encodings ∨ 5 ∈ metadata.encodings ∨ 9 ∈ metadata.encodings) :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.checkGroup_encodings checked

/-- Codec-6 pages retain the checked source frame, stored CRC, prepared layout and ordered selected scalar values. -/
theorem decodeZstd_wire {scalars : Limits} {limits : ScalarPage.Limits} {bound : Bound}
    {encoding : Encoding} {frame : Parquet.Page.Frame} {ordinal : Nat} {slots : List (Option Int64)}
    (read : decodeZstd scalars limits bound encoding frame ordinal = .ok slots) :
    slots.length = Leaf.Internal.pageSlots frame ∧ ZstdWire scalars limits bound encoding frame slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.decodeZstd_wire read

/-- GZIP consumes the exact whole V1 member or the flag-selected V2 suffix after the original raw levels. -/
theorem gzipWire_extents {scalars : Limits} {limits : ScalarPage.Limits} {bound : Bound}
    {declared : List Int} {frame : Parquet.Page.Frame} {slots : List (Option Int64)}
    (wire : PageWire scalars limits bound 2 declared frame slots) :
    let stored := Leaf.Internal.body bound frame
    ∃ (prepared : ScalarPage.Prepared) (layout : FlatPage.Layout),
      slots.map Option.isSome = prepared.mask ∧
      match frame.value.kind with
      | .dataV1 header => ∃ body sections,
        stored.length = frame.value.compressedSize ∧ body.length = frame.value.uncompressedSize ∧
        Compression.Gzip.decoder stored.toList = some (body, []) ∧
        FlatPage.split layout limits.levels.bytes (.v1 (Bytes.ofList body)) = .ok sections ∧
        FlatPage.readMask layout header.numValues limits.levels sections.definitions = .ok prepared.mask ∧
        prepared.scalars = sections.scalars
      | .dataV2 header =>
        header.repetitionBytes = 0 ∧ header.definitionBytes ≤ frame.value.compressedSize ∧
        header.definitionBytes ≤ frame.value.uncompressedSize ∧
        ∃ (definitions : Bytes) (suffix : List UInt8),
          definitions.length = header.definitionBytes ∧ stored.toList = definitions.toList ++ suffix ∧
          FlatPage.readMask layout header.numValues limits.levels definitions = .ok prepared.mask ∧
          prepared.mask.count true = header.numValues - header.numNulls ∧
          suffix.length = frame.value.compressedSize - header.definitionBytes ∧
          prepared.scalars.length = frame.value.uncompressedSize - header.definitionBytes ∧
          (if header.isCompressed then Compression.Gzip.decoder suffix = some (prepared.scalars.toList, [])
           else suffix = prepared.scalars.toList)
      | _ => False :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.gzipWire_extents wire

/-- Zstandard consumes the exact whole V1 frame or the flag-selected V2 suffix after the original raw levels. -/
theorem zstdWire_extents {scalars : Limits} {limits : ScalarPage.Limits} {bound : Bound}
    {encoding : Encoding} {frame : Parquet.Page.Frame} {slots : List (Option Int64)}
    (wire : ZstdWire scalars limits bound encoding frame slots) :
    let stored := Leaf.Internal.body bound frame
    let sizes : ScalarPage.Sizes := ⟨frame.value.compressedSize, frame.value.uncompressedSize⟩
    ∃ (prepared : ScalarPage.Prepared) (layout : FlatPage.Layout) (values : List Int64),
      ZstdValuesWire scalars encoding prepared values ∧ slots.map Option.isSome = prepared.mask ∧
      slots.filterMap id = values ∧
      match frame.value.kind with
      | .dataV1 header => ∃ expanded sections,
        FlatColumn.Zstd.PayloadWire scalars.zstd (limits.payloadBounds sizes 0) 6 stored.toList expanded ∧
        FlatPage.split layout limits.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
        FlatPage.readMask layout header.numValues limits.levels sections.definitions = .ok prepared.mask ∧
        prepared.scalars = sections.scalars
      | .dataV2 header =>
        header.repetitionBytes = 0 ∧ header.definitionBytes ≤ frame.value.compressedSize ∧
        header.definitionBytes ≤ frame.value.uncompressedSize ∧
        ∃ (definitions : Bytes) (suffix : List UInt8),
          definitions.length = header.definitionBytes ∧ stored.toList = definitions.toList ++ suffix ∧
          FlatPage.readMask layout header.numValues limits.levels definitions = .ok prepared.mask ∧
          prepared.mask.count true = header.numValues - header.numNulls ∧
          FlatColumn.Zstd.PayloadWire scalars.zstd (limits.payloadBounds sizes header.definitionBytes)
            (ScalarPage.v2Codec 6 (some header.isCompressed)) suffix prepared.scalars.toList
      | _ => False :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.zstdWire_extents wire

/-- Successful standalone GZIP PLAIN V2 agrees at the same GZIP controller limit and declared PLAIN tag. -/
theorem readGroup_agrees_gzip_v2 {scalars : Limits} {strict : Leaf.Gzip.V2.Limits}
    {limits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (fuel : scalars.gzipCalls = strict.gzipCalls)
    (advertised : ∀ chunk, Leaf.selectChunkWith .gzipPlainV2 limits bound index = .ok chunk →
      0 ∈ chunk.column.metadata.encodings)
    (accepted : Leaf.Gzip.V2.readGroup strict limits bound index = .ok slots) :
    readGroup scalars limits bound index = .ok slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.readGroup_agrees_gzip_v2 fuel advertised accepted

/-- Successful standalone Zstandard PLAIN V2 agrees at the same frame limits and declared PLAIN tag. -/
theorem readGroup_agrees_zstd_v2 {scalars : Limits} {strict : Leaf.Zstd.V2.Limits}
    {limits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (compression : scalars.zstd = strict.compression)
    (advertised : ∀ chunk, Leaf.selectChunkWith .zstdPlainV2 limits bound index = .ok chunk →
      0 ∈ chunk.column.metadata.encodings)
    (accepted : Leaf.Zstd.V2.readGroup strict limits bound index = .ok slots) :
    readGroup scalars limits bound index = .ok slots :=
  Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.readGroup_agrees_zstd_v2 compression advertised accepted

end Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch
