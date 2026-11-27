module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.V2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.ByteStreamSplit.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Delta.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Silmaril.Formats.Parquet.FlatColumn.Zstd.Thms
import Silmaril.Formats.Parquet.DeltaBinaryPacked.Thms
import Silmaril.Formats.Parquet.ByteStreamSplit.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Thms
import Silmaril.Formats.Parquet.Timestamp.Page.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Footer.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Numeric.Timestamp (Ticks)
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

private theorem scalarDispatch_metadata {metadata : Footer.ColumnMetadata} {rows : Int} :
    Leaf.ChunkEncoding.scalarDispatch.admitsMetadata metadata rows = true ↔
      metadata.indexPageOffset = none ∧ metadata.dictionaryPageOffset = none ∧
      (∀ tag ∈ metadata.encodings, tag = 0 ∨ tag = 3 ∨ tag = 5 ∨ tag = 9) ∧
      (0 ∈ metadata.encodings ∨ 5 ∈ metadata.encodings ∨ 9 ∈ metadata.encodings) := by
  simp [Leaf.ChunkEncoding.scalarDispatch_admitsMetadata, List.all_eq_true, and_left_comm, and_comm, or_assoc]

private theorem scalarDispatch_widen {metadata : Footer.ColumnMetadata} {rows tag : Int}
    {encoding : Leaf.ChunkEncoding}
    (arm : (encoding, tag) ∈ [(Leaf.ChunkEncoding.plain, 0), (.deltaBinaryPacked, 5), (.byteStreamSplit, 9)])
    (strict : encoding.admitsMetadata metadata rows = true)
    (plainDeclared : encoding = .plain → 0 ∈ metadata.encodings) :
    Leaf.ChunkEncoding.scalarDispatch.admitsMetadata metadata rows = true ∧ tag ∈ metadata.encodings := by
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at arm
  simp only [scalarDispatch_metadata]
  rcases arm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have ⟨index, permitted, _, dict⟩ : metadata.indexPageOffset = none ∧
        (∀ id ∈ metadata.encodings, id = 0 ∨ id = 3) ∧
        (rows = 0 ∨ 0 ∈ metadata.encodings) ∧ metadata.dictionaryPageOffset = none := by
      simpa [Leaf.ChunkEncoding.plain_admitsMetadata, List.all_eq_true, and_assoc] using strict
    have tag := plainDeclared rfl
    exact ⟨⟨index, dict, fun id member => (permitted id member).imp_right Or.inl, .inl tag⟩, tag⟩
  · have ⟨index, permitted, tag, dict⟩ : metadata.indexPageOffset = none ∧
        (∀ id ∈ metadata.encodings, id = 3 ∨ id = 5) ∧
        5 ∈ metadata.encodings ∧ metadata.dictionaryPageOffset = none := by
      simpa [Leaf.ChunkEncoding.delta_admitsMetadata, List.all_eq_true, and_assoc] using strict
    exact ⟨⟨index, dict, fun id member => .inr ((permitted id member).imp_right Or.inl),
      .inr (.inl tag)⟩, tag⟩
  · have ⟨index, permitted, tag, dict⟩ : metadata.indexPageOffset = none ∧
        (∀ id ∈ metadata.encodings, id = 3 ∨ id = 9) ∧
        9 ∈ metadata.encodings ∧ metadata.dictionaryPageOffset = none := by
      simpa [Leaf.ChunkEncoding.split_admitsMetadata, List.all_eq_true, and_assoc] using strict
    exact ⟨⟨index, dict, fun id member => .inr ((permitted id member).imp_right Or.inr),
      .inr (.inr tag)⟩, tag⟩

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
      (group.frames.map Leaf.Internal.pageSlots).sum = group.chunk.group.numRows.toNat := by
  unfold checkGroup at checked
  obtain ⟨chunk, selected, checked⟩ := bind_ok checked
  obtain ⟨frames, parsed, checked⟩ := bind_ok checked
  have wire := mapError_ok parsed
  by_cases rows : (frames.map Leaf.Internal.pageSlots).sum = chunk.group.numRows.toNat
  · simp [rows, pure, Except.pure] at checked
    subst group
    obtain ⟨original, column, _, _, _, codec, metadata, _, span, _⟩ := Leaf.selectChunkWith_sound selected
    have noDict := (scalarDispatch_metadata.mp metadata).2.1
    have offset := Footer.checkDataSpan_some_iff.mp (by
      simpa [Parquet.Page.columnSpan, noDict] using span)
    exact ⟨selected, original, column, by simpa [Leaf.ChunkEncoding.admitsCodec, or_assoc] using codec,
      noDict, offset.1, offset.2.1, wire, (Parquet.Page.readChunk_chain wire).2.2, rows⟩
  · simp [rows, Bind.bind, Except.bind] at checked

theorem checkGroup_encodings {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {group : CheckedGroup} (checked : checkGroup limits bound index = .ok group) :
    let metadata := group.chunk.column.metadata
    metadata.indexPageOffset = none ∧ metadata.dictionaryPageOffset = none ∧
      (∀ tag ∈ metadata.encodings, tag = 0 ∨ tag = 3 ∨ tag = 5 ∨ tag = 9) ∧
      (0 ∈ metadata.encodings ∨ 5 ∈ metadata.encodings ∨ 9 ∈ metadata.encodings) := by
  have selected := (checkGroup_wire checked).1
  exact scalarDispatch_metadata.mp (Leaf.selectChunkWith_sound selected).2.2.2.2.2.2.1

private theorem parameter_tag {bound : Bound} {frame : Parquet.Page.Frame} {codec : Int}
    {params : ScalarPage.Parameters}
    (checked : Timestamp.Page.parameters bound.binding.leaf bound.levels codec frame.value = .ok params) :
    pageTag frame = some params.encoding ∧ params.numValues = Leaf.Internal.pageSlots frame := by
  have header := (Timestamp.Page.parameters_sound checked).2.2.2.2
  cases kind : frame.value.kind <;> simp [pageTag, Leaf.Internal.pageSlots, kind] at header ⊢
  all_goals exact ⟨header.2.1.symm, header.1⟩

theorem route_ok_iff {declared : List Int} {frame : Parquet.Page.Frame} {ordinal : Nat} {encoding : Encoding} :
    route declared frame ordinal = .ok encoding ↔
      pageTag frame = some encoding.tag ∧ encoding.tag ∈ declared := by
  cases tag : pageTag frame with
  | none => simp [route, tag]
  | some value =>
    by_cases advertised : value ∈ declared
    · cases encoding <;> by_cases zero : value = 0 <;> by_cases delta : value = 5 <;>
        by_cases split : value = 9 <;> simp_all [route, Encoding.tag, Encoding.ofTag]
    · have different : ¬ (value = encoding.tag ∧ encoding.tag ∈ declared) :=
        fun ⟨same, present⟩ => advertised (same ▸ present)
      cases selected : Encoding.ofTag value <;> simp [route, tag, selected, advertised, different]

private theorem decodePlain_wire {limits : ScalarPage.Limits}
    {bound : Bound} {codec : Int} {frame : Parquet.Page.Frame} {ordinal : Nat}
    {slots : List (Option Int64)} (read : decodePlain limits bound codec frame ordinal = .ok slots) :
    slots.length = Leaf.Internal.pageSlots frame ∧ PlainWire limits bound codec frame slots := by
  unfold decodePlain at read
  obtain ⟨status, verified, read⟩ := bind_ok read
  obtain ⟨params, admitted, read⟩ := bind_ok read
  have parsed := mapError_ok admitted
  have decoded := mapError_ok read
  obtain ⟨slice, size, cap, crc⟩ := Leaf.Dictionary.Snappy.stored_verified (mapError_ok verified)
  obtain ⟨prepared, words, prep, present, mask, values, _, _⟩ := ScalarPage.decode_sound decoded
  obtain ⟨layout, valid, exactLayout⟩ := ScalarPage.prepare_sound prep
  have tag : params.encoding = 0 := by
    by_contra wrong
    simp [ScalarPage.validate, ScalarPage.validateFor, wrong] at valid
  exact ⟨(ScalarPage.decode_counts decoded).1.trans (parameter_tag parsed).2,
    status, params, layout, prepared, words, mapError_ok verified, slice, size, cap,
    by cases status <;> exact crc, parsed, tag, valid, exactLayout, present, mask, values⟩

private theorem decodeZstdValues_wire {scalars : Limits} {encoding : Encoding}
    {prepared : ScalarPage.Prepared} {frame : Parquet.Page.Frame} {ordinal : Nat} {values : List Int64}
    (read : decodeZstdValues scalars encoding prepared frame ordinal = .ok values) :
    ZstdValuesWire scalars encoding prepared values := by
  cases encoding with
  | plain =>
    have read := mapError_ok read
    have words := Plain.decodeFixedWidth_ok_iff.mp read
    obtain ⟨_, bytes, _, count, _, ordered⟩ := words
    exact ⟨by rw [ordered, List.length_map, count], read⟩
  | delta =>
    have read := mapError_ok read
    obtain ⟨stream, bytes, wire, valid, reconstructed, count⟩ := DeltaBinaryPacked.decode_sound read
    exact ⟨count, stream, bytes, wire, valid, reconstructed⟩
  | split =>
    have read := mapError_ok read
    obtain ⟨words, admitted, lanes, ordered, count⟩ := Parquet.ByteStreamSplit.decode_sound read
    exact ⟨count, words, admitted, lanes, ordered⟩

private theorem zstd_mask_length {limits : FlatColumn.Zstd.Limits} {params : ScalarPage.Parameters}
    {layout : FlatPage.Layout} {stored : Bytes} {prepared : ScalarPage.Prepared}
    (wire : FlatColumn.Zstd.PreparedWire limits params layout stored prepared) :
    prepared.mask.length = params.numValues := by
  cases version : params.version with
  | v1 _ _ =>
    simp only [FlatColumn.Zstd.PreparedWire, version] at wire
    obtain ⟨_, _, _, _, _, _, mask, _⟩ := wire
    exact FlatPage.readMask_length mask
  | v2 _ _ _ _ _ =>
    simp only [FlatColumn.Zstd.PreparedWire, version] at wire
    obtain ⟨_, _, _, _, _, _, _, _, _, _, mask, _, _⟩ := wire
    exact FlatPage.readMask_length mask

theorem decodeZstd_wire {scalars : Limits} {limits : ScalarPage.Limits} {bound : Bound}
    {encoding : Encoding} {frame : Parquet.Page.Frame} {ordinal : Nat} {slots : List (Option Int64)}
    (read : decodeZstd scalars limits bound encoding frame ordinal = .ok slots) :
    slots.length = Leaf.Internal.pageSlots frame ∧ ZstdWire scalars limits bound encoding frame slots := by
  unfold decodeZstd at read
  obtain ⟨status, verified, read⟩ := bind_ok read
  obtain ⟨params, admitted, read⟩ := bind_ok read
  obtain ⟨prepared, prep, read⟩ := bind_ok read
  obtain ⟨values, decoded, restored⟩ := bind_ok read
  have parsed := mapError_ok admitted
  obtain ⟨_, layout, valid, _, _, expanded, exactLayout⟩ := FlatColumn.Zstd.prepareFor_sound (mapError_ok prep)
  obtain ⟨mask, ordered⟩ := FlatPage.reconstruct_ok_iff.mp (mapError_ok restored)
  obtain ⟨slice, size, cap, crc⟩ := Leaf.Dictionary.Snappy.stored_verified (mapError_ok verified)
  have tag : params.encoding = encoding.tag := by
    by_contra wrong
    simp [ScalarPage.validateFor, wrong] at valid
  have counts := congrArg List.length mask
  rw [List.length_map, zstd_mask_length exactLayout, (parameter_tag parsed).2] at counts
  have expandedFits : frame.value.uncompressedSize ≤ limits.uncompressedBytes := by
    simpa only [(Timestamp.Page.parameters_sound parsed).2.2.2.1, Limits.zstdPage] using expanded
  exact ⟨counts, status, params, layout, prepared, values, mapError_ok verified,
    slice, size, cap, expandedFits, by cases status <;> exact crc, parsed, tag, valid, exactLayout,
    decodeZstdValues_wire decoded, mask, ordered⟩

theorem decodePage_wire {scalars : Limits} {limits : ScalarPage.Limits}
    {bound : Bound} {codec : Int} {declared : List Int} {frame : Parquet.Page.Frame} {ordinal : Nat}
    {slots : List (Option Int64)} (read : decodePage scalars limits bound codec declared frame ordinal = .ok slots) :
    PageWire scalars limits bound codec declared frame slots := by
  unfold decodePage at read
  obtain ⟨encoding, chosen, read⟩ := bind_ok read
  have ⟨tag, advertised⟩ := route_ok_iff.mp chosen
  by_cases zstd : codec = 6
  · simp only [decodeSelected, ite_eq_left zstd] at read
    obtain ⟨count, wire⟩ := decodeZstd_wire read
    exact ⟨count, encoding, tag, advertised, by simp only [ite_eq_left zstd]; exact wire⟩
  simp only [decodeSelected, ite_eq_right zstd] at read
  cases encoding with
  | plain =>
    have ⟨count, wire⟩ := decodePlain_wire read
    exact ⟨count, .plain, tag, advertised, by simpa only [ite_eq_right zstd] using wire⟩
  | delta =>
    have wire := Leaf.Delta.decodePage_wire read
    have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, count, _⟩ := wire
    exact ⟨count, .delta, tag, advertised, by simpa only [ite_eq_right zstd] using wire⟩
  | split =>
    have wire := Leaf.ByteStreamSplit.decodePage_wire read
    have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, count, _⟩ := wire
    exact ⟨count, .split, tag, advertised, by simpa only [ite_eq_right zstd] using wire⟩

theorem readGroup_wire {scalars : Limits} {limits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (read : readGroup scalars limits bound index = .ok slots) :
    ∃ group pages, checkGroup limits bound index = .ok group ∧
      List.Forall₂ (PageWire scalars limits.page bound group.chunk.column.metadata.codec
        group.chunk.column.metadata.encodings) group.frames pages ∧
      slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
      slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
      slots.length = group.chunk.group.numRows.toNat := by
  unfold readGroup at read
  obtain ⟨group, checked, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  have raw : List.Forall₂ (PageWire scalars limits.page bound group.chunk.column.metadata.codec
        group.chunk.column.metadata.encodings) group.frames pages := by
    rw [← List.zipIdx_map_fst 0 group.frames, List.forall₂_map_left_iff]
    exact (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun _ _ read => decodePage_wire read
  have counts : pages.map List.length = group.frames.map Leaf.Internal.pageSlots := by
    clear read checked decoded
    generalize group.frames = frames at raw ⊢
    induction raw with
    | nil => rfl
    | cons head _ ih =>
      exact congrArg₂ List.cons head.1 ih
  have mapped := (Except.ok.inj read).symm
  refine ⟨group, pages, checked, raw, mapped, ?_, ?_⟩
  · rw [mapped, List.map_map]
    apply List.map_congr_left
    intro slot _
    cases slot <;> rfl
  · obtain ⟨_, _, _, _, _, _, _, _, _, rows⟩ := checkGroup_wire checked
    rw [mapped, List.length_map, List.length_flatten, counts, rows]

theorem readGroup_first_page_error {scalars : Limits} {limits : Leaf.Limits} {bound : Bound} {index ordinal : Nat}
    {group : CheckedGroup} {frame : Parquet.Page.Frame} {before after : List (Parquet.Page.Frame × Nat)}
    {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (checked : checkGroup limits bound index = .ok group)
    (split : group.frames.zipIdx = before ++ (frame, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => decodePage scalars limits.page bound group.chunk.column.metadata.codec group.chunk.column.metadata.encodings item i) = .ok outputs)
    (failed : decodePage scalars limits.page bound group.chunk.column.metadata.codec group.chunk.column.metadata.encodings frame ordinal = .error cause) :
    readGroup scalars limits bound index = .error cause := by
  simp [readGroup, checked, split, earlier, failed, Bind.bind, Except.bind]

private theorem codec_iff {limits : Leaf.Limits} {codec : Int} :
    Leaf.ChunkEncoding.scalarDispatch.admitsCodec limits codec = true ↔
      codec = 0 ∨ codec = 1 ∨ codec = 2 ∨ codec = 6 := by
  simp [Leaf.ChunkEncoding.admitsCodec, or_assoc]

private theorem checkGroup_of_selection {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {mode : Leaf.ChunkEncoding} {chunk : Leaf.Chunk} {frames : List Parquet.Page.Frame}
    (picked : Leaf.selectChunkWith mode limits bound index = .ok chunk)
    (allowed : Leaf.ChunkEncoding.scalarDispatch.admitsCodec limits chunk.column.metadata.codec = true)
    (admitted : Leaf.ChunkEncoding.scalarDispatch.admitsMetadata chunk.column.metadata chunk.group.numRows = true)
    (framed : Parquet.Page.readChunk limits.framing bound.snapshot.bytes chunk.span = .ok frames)
    (counts : (frames.map Leaf.Internal.pageSlots).sum = chunk.group.numRows.toNat) :
    checkGroup limits bound index = .ok ⟨chunk, frames⟩ := by
  obtain ⟨group, column, path, physical, values, _, _, rowCap, span, disjoint⟩ :=
    Leaf.selectChunkWith_sound picked
  have selected : Leaf.selectChunkWith .scalarDispatch limits bound index = .ok chunk := by
    cases chunk
    simp only at path physical values
    simp [Leaf.selectChunkWith, group, column, path, physical, values, allowed, admitted, span,
      disjoint, Nat.not_lt.mpr rowCap, pure, Except.pure]
  simp [checkGroup, selected, framed, counts, Except.mapError, Bind.bind, Except.bind, pure, Except.pure]

private theorem widenGroup {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {mode : Leaf.ChunkEncoding} {tag : Int} {chunk : Leaf.Chunk} {frames : List Parquet.Page.Frame}
    (arm : (mode, tag) ∈ [(Leaf.ChunkEncoding.plain, 0), (.deltaBinaryPacked, 5), (.byteStreamSplit, 9)])
    (picked : Leaf.selectChunkWith mode limits bound index = .ok chunk)
    (framed : Parquet.Page.readChunk limits.framing bound.snapshot.bytes chunk.span = .ok frames)
    (counts : (frames.map Leaf.Internal.pageSlots).sum = chunk.group.numRows.toNat)
    (plainDeclared : mode = .plain → 0 ∈ chunk.column.metadata.encodings) :
    checkGroup limits bound index = .ok ⟨chunk, frames⟩ ∧ tag ∈ chunk.column.metadata.encodings := by
  obtain ⟨_, _, _, _, _, codec, metadata, _, _, _⟩ := Leaf.selectChunkWith_sound picked
  obtain ⟨metadata', advertised⟩ := scalarDispatch_widen arm metadata plainDeclared
  have old : chunk.column.metadata.codec = 0 ∨ chunk.column.metadata.codec = 1 := by
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at arm
    rcases arm with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · simp [Leaf.ChunkEncoding.admitsCodec, Leaf.Limits.admitsCodec] at codec
      exact codec.imp_right And.right
    · simpa [Leaf.ChunkEncoding.admitsCodec] using codec
    · simpa [Leaf.ChunkEncoding.admitsCodec] using codec
  have codec' : Leaf.ChunkEncoding.scalarDispatch.admitsCodec limits chunk.column.metadata.codec = true :=
    codec_iff.mpr (old.imp_right Or.inl)
  exact ⟨checkGroup_of_selection picked codec' metadata' framed counts, advertised⟩

private theorem finishGroup {scalars : Limits} {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {group : CheckedGroup} {pages : List (List (Option Int64))}
    (checked : checkGroup limits bound index = .ok group)
    (decoded : group.frames.zipIdx.mapM (fun (frame, ordinal) =>
      decodePage scalars limits.page bound group.chunk.column.metadata.codec
        group.chunk.column.metadata.encodings frame ordinal) = .ok pages) :
    readGroup scalars limits bound index =
      .ok (pages.flatten.map (Option.map bound.binding.descriptor.decode)) := by
  simp [readGroup, checked, decoded, Bind.bind, Except.bind, pure, Except.pure]

theorem readGroup_agrees_delta {scalars : Limits} {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {slots : Slots bound} (accepted : Leaf.Delta.readGroup scalars.delta limits bound index = .ok slots) :
    readGroup scalars limits bound index = .ok slots := by
  unfold Leaf.Delta.readGroup at accepted
  obtain ⟨group, checked, accepted⟩ := bind_ok accepted
  obtain ⟨pages, decoded, accepted⟩ := bind_ok accepted
  obtain ⟨selected, _, _, codec, _, _, _, framed, _, counts⟩ := Leaf.Delta.checkGroup_wire checked
  have ⟨admitted, declared⟩ := widenGroup (tag := 5) (by simp) selected framed counts (by simp)
  have noGzip : group.chunk.column.metadata.codec ≠ 2 := by rcases codec with h | h <;> simp [h]
  have noZstd : group.chunk.column.metadata.codec ≠ 6 := by rcases codec with h | h <;> simp [h]
  have followed : List.Forall₂ (fun (frame, ordinal) raw =>
      decodePage scalars limits.page bound group.chunk.column.metadata.codec
        group.chunk.column.metadata.encodings frame ordinal = .ok raw) group.frames.zipIdx pages :=
    (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun (frame, ordinal) _ read => by
    have ⟨_, params, _, _, _, _, _, _, _, _, parsed, tag, _⟩ := Leaf.Delta.decodePage_wire read
    have chosen : route group.chunk.column.metadata.encodings frame ordinal = .ok .delta :=
      route_ok_iff.mpr ⟨(parameter_tag parsed).1.trans (congrArg some tag), declared⟩
    simpa [decodePage, chosen, decodeSelected, Limits.pageFor, noGzip, noZstd, Bind.bind, Except.bind] using read
  exact (finishGroup admitted (List.mapM_eq_ok_iff_forall₂.mpr followed)).trans accepted

theorem readGroup_agrees_split {scalars : Limits} {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {slots : Slots bound} (accepted : Leaf.ByteStreamSplit.readGroup scalars.split limits bound index = .ok slots) :
    readGroup scalars limits bound index = .ok slots := by
  unfold Leaf.ByteStreamSplit.readGroup at accepted
  obtain ⟨group, checked, accepted⟩ := bind_ok accepted
  obtain ⟨pages, decoded, accepted⟩ := bind_ok accepted
  obtain ⟨selected, _, _, codec, _, _, _, framed, _, counts⟩ := Leaf.ByteStreamSplit.checkGroup_wire checked
  have ⟨admitted, declared⟩ := widenGroup (tag := 9) (by simp) selected framed counts (by simp)
  have noGzip : group.chunk.column.metadata.codec ≠ 2 := by rcases codec with h | h <;> simp [h]
  have noZstd : group.chunk.column.metadata.codec ≠ 6 := by rcases codec with h | h <;> simp [h]
  have followed : List.Forall₂ (fun (frame, ordinal) raw =>
      decodePage scalars limits.page bound group.chunk.column.metadata.codec
        group.chunk.column.metadata.encodings frame ordinal = .ok raw) group.frames.zipIdx pages :=
    (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun (frame, ordinal) _ read => by
    have ⟨_, params, _, _, _, _, _, _, _, _, parsed, tag, _⟩ := Leaf.ByteStreamSplit.decodePage_wire read
    have chosen : route group.chunk.column.metadata.encodings frame ordinal = .ok .split :=
      route_ok_iff.mpr ⟨(parameter_tag parsed).1.trans (congrArg some tag), declared⟩
    simpa [decodePage, chosen, decodeSelected, Limits.pageFor, noGzip, noZstd, Bind.bind, Except.bind] using read
  exact (finishGroup admitted (List.mapM_eq_ok_iff_forall₂.mpr followed)).trans accepted

private theorem plainAdmission {params : ScalarPage.Parameters} {limits : ScalarPage.Limits}
    {source : Bytes} {slots : List (Option Int64)}
    (decoded : ScalarPage.decode .int64 params limits source = .ok slots) :
    params.encoding = 0 ∧ params.sizes.compressed ≤ limits.compressedBytes := by
  obtain ⟨prepared, _, prep, _⟩ := ScalarPage.decode_sound decoded
  obtain ⟨layout, valid, _⟩ := ScalarPage.prepare_sound prep
  have tag : params.encoding = 0 := by
    by_contra bad
    simp [ScalarPage.validate, ScalarPage.validateFor, bad] at valid
  refine ⟨tag, ?_⟩
  by_contra! bad
  simp [ScalarPage.validate, ScalarPage.validateFor, tag, bad] at valid
  split at valid <;> contradiction

private theorem decodePage_agrees_plain {scalars : Limits} {limits : ScalarPage.Limits}
    {bound : Bound} {codec : Int} {declared : List Int} {frame : Parquet.Page.Frame} {ordinal : Nat}
    {status : Parquet.Page.Checksum.Status} {params : ScalarPage.Parameters} {slots : List (Option Int64)}
    (advertised : 0 ∈ declared) (noZstd : codec ≠ 6)
    (verified : Parquet.Page.Checksum.verify (scalars.pageFor limits codec).compressedBytes bound.snapshot.bytes frame = .ok status)
    (parsed : Timestamp.Page.parameters bound.binding.leaf bound.levels codec frame.value = .ok params)
    (read : ScalarPage.decode .int64 params (scalars.pageFor limits codec) (Leaf.Internal.body bound frame) = .ok slots) :
    decodePage scalars limits bound codec declared frame ordinal = .ok slots := by
  have tag := (plainAdmission read).1
  have routed : route declared frame ordinal = .ok .plain :=
    route_ok_iff.mpr ⟨(parameter_tag parsed).1.trans (congrArg some tag), advertised⟩
  simp [decodePage, routed, decodeSelected, noZstd, decodePlain, verified, parsed, read, Except.mapError, Bind.bind, Except.bind]

private def PlainAccepted (limits : ScalarPage.Limits) (bound : Bound) (codec : Int)
    (frame : Parquet.Page.Frame) (slots : List (Option Int64)) : Prop :=
  ∃ status params,
    Parquet.Page.Checksum.verify limits.compressedBytes bound.snapshot.bytes frame = .ok status ∧
    Timestamp.Page.parameters bound.binding.leaf bound.levels codec frame.value = .ok params ∧
    ScalarPage.decode .int64 params limits (Leaf.Internal.body bound frame) = .ok slots

private theorem readGroup_agrees_plain_frames {scalars : Limits} {limits : Leaf.Limits} {bound : Bound}
    {index : Nat} {chunk : Leaf.Chunk} {frames : List Parquet.Page.Frame} {pages : List (List (Option Int64))}
    (picked : Leaf.selectChunk limits bound index = .ok chunk)
    (framed : Parquet.Page.readChunk limits.framing bound.snapshot.bytes chunk.span = .ok frames)
    (counts : (frames.map Leaf.Internal.pageSlots).sum = chunk.group.numRows.toNat)
    (advertised : 0 ∈ chunk.column.metadata.encodings)
    (physical : List.Forall₂ (PlainAccepted limits.page bound chunk.column.metadata.codec) frames pages) :
    readGroup scalars limits bound index = .ok (pages.flatten.map (Option.map bound.binding.descriptor.decode)) := by
  have ⟨checked, advertised⟩ := widenGroup (tag := 0) (by simp) picked framed counts (fun _ => advertised)
  rw [← List.zipIdx_map_fst 0 frames, List.forall₂_map_left_iff] at physical
  apply finishGroup checked
  apply List.mapM_eq_ok_iff_forall₂.mpr
  have codecs := (Leaf.selectChunk_sound picked).2.2.2.2.2.1
  have allowed : chunk.column.metadata.codec = 0 ∨ chunk.column.metadata.codec = 1 := by
    simp [Leaf.Limits.admitsCodec] at codecs
    exact codecs.imp_right And.right
  have noGzip : chunk.column.metadata.codec ≠ 2 := by rcases allowed with h | h <;> simp [h]
  have noZstd : chunk.column.metadata.codec ≠ 6 := by rcases allowed with h | h <;> simp [h]
  exact physical.imp fun _ _ ⟨_, _, verified, parsed, read⟩ =>
    decodePage_agrees_plain advertised noZstd (by simpa [Limits.pageFor, noGzip] using verified)
      parsed (by simpa [Limits.pageFor, noGzip] using read)

private theorem plainPhysicalCounts {limits : ScalarPage.Limits} {bound : Bound} {codec : Int}
    {frames : List Parquet.Page.Frame} {pages : List (List (Option Int64))}
    (physical : List.Forall₂ (Leaf.PhysicalFrame limits bound codec) frames pages) :
    pages.map List.length = frames.map Leaf.Internal.pageSlots := by
  induction physical with
  | nil => rfl
  | cons head _ ih =>
    obtain ⟨_, _, parsed, read⟩ := head
    exact congrArg₂ List.cons ((ScalarPage.decode_counts read).1.trans (parameter_tag parsed).2) ih

private theorem plainAccepted_of_physical {limits : ScalarPage.Limits} {bound : Bound} {codec : Int}
    {frames : List Parquet.Page.Frame} {pages : List (List (Option Int64))}
    (physical : List.Forall₂ (Leaf.PhysicalFrame limits bound codec) frames pages)
    (within : ∀ frame ∈ frames, Parquet.Page.Checksum.PayloadWithin bound.snapshot.bytes frame) :
    List.Forall₂ (PlainAccepted limits bound codec) frames pages := by
  induction physical with
  | nil => exact .nil
  | @cons frame slots frames pages head _ ih =>
    obtain ⟨crc, params, parsed, decoded⟩ := head
    have cap := (Timestamp.Page.parameters_sound parsed).2.2.2.1 ▸ (plainAdmission decoded).2
    have verified := Parquet.Page.Checksum.verify_absent_iff.mpr
      ⟨cap, within frame (by simp), crc⟩
    exact .cons ⟨.absent, params, verified, parsed, decoded⟩
      (ih fun item member => within item (List.mem_cons_of_mem _ member))

theorem readGroup_agrees_plain {scalars : Limits} {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    {slots : Slots bound}
    (advertised : ∀ chunk, Leaf.selectChunk limits bound index = .ok chunk → 0 ∈ chunk.column.metadata.encodings)
    (accepted : Leaf.readGroup limits bound index = .ok slots) :
    readGroup scalars limits bound index = .ok slots := by
  obtain ⟨chunk, frames, pages, picked, framed, _, physical, mapped, rows⟩ := Leaf.readGroup_sound accepted
  have counts : (frames.map Leaf.Internal.pageSlots).sum = chunk.group.numRows.toNat := by
    rw [← plainPhysicalCounts physical, ← List.length_flatten]
    rw [mapped, List.length_map] at rows
    exact rows
  have extents (frame : Parquet.Page.Frame) (mem : frame ∈ frames) :=
    Parquet.Page.Checksum.payloadWithin_of_frameWithin (Parquet.Page.readChunk_payloads_bounded framed frame mem)
      (Parquet.Page.readChunk_chain framed).2.1
  rw [mapped]
  exact readGroup_agrees_plain_frames picked framed counts (advertised chunk picked)
    (plainAccepted_of_physical physical extents)

private theorem readGroup_allowSnappy {scalars : Limits} {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    (allow : Bool) :
    readGroup scalars {limits with allowSnappy := allow} bound index =
      readGroup scalars limits bound index := by
  cases limits
  rfl

theorem readGroup_agrees_plain_v2_uncompressed {scalars : Limits} {limits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound}
    (advertised : ∀ chunk, Leaf.selectChunk {limits with allowSnappy := false} bound index = .ok chunk →
      0 ∈ chunk.column.metadata.encodings)
    (accepted : Leaf.Uncompressed.V2.readGroup limits bound index = .ok slots) :
    readGroup scalars limits bound index = .ok slots := by
  obtain ⟨group, pages, checked, physical, mapped, _⟩ := Leaf.Uncompressed.V2.readGroup_wire accepted
  obtain ⟨picked, codec, _, _, framed, _, counts⟩ := Leaf.Uncompressed.V2.checkGroup_wire checked
  rw [mapped, ← readGroup_allowSnappy false]
  apply readGroup_agrees_plain_frames picked framed counts (advertised _ picked)
  rw [codec]
  exact physical.imp fun _ _ ⟨_, status, params, _, verified, parsed, decoded, _⟩ =>
    ⟨status, params, verified, parsed, decoded⟩

theorem readGroup_agrees_plain_v2_snappy {scalars : Limits} {limits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound}
    (advertised : ∀ chunk, Leaf.selectChunk {limits with allowSnappy := true} bound index = .ok chunk →
      0 ∈ chunk.column.metadata.encodings)
    (accepted : Leaf.SnappyV2.readGroup limits bound index = .ok slots) :
    readGroup scalars limits bound index = .ok slots := by
  obtain ⟨group, pages, checked, physical, mapped, _⟩ := Leaf.SnappyV2.readGroup_wire accepted
  obtain ⟨picked, codec, framed, _, counts⟩ := Leaf.SnappyV2.checkGroup_wire checked
  rw [mapped, ← readGroup_allowSnappy true]
  apply readGroup_agrees_plain_frames picked framed counts (advertised _ picked)
  rw [codec]
  exact physical.imp fun _ _ ⟨_, status, params, _, verified, parsed, decoded, _⟩ =>
    ⟨status, params, verified, parsed, decoded⟩

private theorem compressedPlainMetadata {mode : Leaf.ChunkEncoding}
    {chunk : Leaf.Chunk} {limits : Leaf.Limits} {bound : Bound} {index : Nat}
    (selected : Leaf.selectChunkWith mode limits bound index = .ok chunk)
    (modePolicy : mode.admitsMetadata chunk.column.metadata chunk.group.numRows =
      Leaf.ChunkEncoding.plain.admitsMetadata chunk.column.metadata chunk.group.numRows)
    (advertised : 0 ∈ chunk.column.metadata.encodings) :
    Leaf.ChunkEncoding.scalarDispatch.admitsMetadata chunk.column.metadata chunk.group.numRows = true := by
  have admitted := (Leaf.selectChunkWith_sound selected).2.2.2.2.2.2.1
  rw [modePolicy] at admitted
  exact (scalarDispatch_widen (encoding := .plain) (tag := 0) (by simp) admitted (fun _ => advertised)).1

private theorem gzip_plan_parameters {bound : Bound} {frame : Parquet.Page.Frame}
    {page : Leaf.Dictionary.DataPage}
    (planned : Leaf.Dictionary.Gzip.V2.planDataWith (· == 0) bound frame = .ok page) :
    Timestamp.Page.parameters bound.binding.leaf bound.levels 2 frame.value = .ok page.params := by
  cases kind : frame.value.kind with
  | dataV2 header =>
    by_cases tag : header.encoding = 0
    · cases parsed : Timestamp.Page.parameters bound.binding.leaf bound.levels Payload.Codec.gzip.id frame.value with
      | error cause =>
        simp [Leaf.Dictionary.Gzip.V2.planDataWith, kind, tag, parsed, Except.mapError, Bind.bind, Except.bind] at planned
      | ok params =>
        simp [Leaf.Dictionary.Gzip.V2.planDataWith, kind, tag, parsed, Except.mapError, Bind.bind,
          Except.bind, pure, Except.pure] at planned
        subst page
        exact parsed
    · simp [Leaf.Dictionary.Gzip.V2.planDataWith, kind, tag, Bind.bind, Except.bind] at planned
  | dataV1 _ | dictionary _ | skipped _ =>
    simp [Leaf.Dictionary.Gzip.V2.planDataWith, kind, Bind.bind, Except.bind] at planned

theorem readGroup_agrees_gzip_v2 {scalars : Limits} {strict : Leaf.Gzip.V2.Limits}
    {limits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (fuel : scalars.gzipCalls = strict.gzipCalls)
    (advertised : ∀ chunk, Leaf.selectChunkWith .gzipPlainV2 limits bound index = .ok chunk →
      0 ∈ chunk.column.metadata.encodings)
    (accepted : Leaf.Gzip.V2.readGroup strict limits bound index = .ok slots) :
    readGroup scalars limits bound index = .ok slots := by
  obtain ⟨group, pages, checked, physical, mapped, _⟩ := Leaf.Gzip.V2.readGroup_wire accepted
  obtain ⟨picked, codec, _, framed, _, counts, _, _⟩ := Leaf.Gzip.V2.checkGroup_wire checked
  have chosen : group.chunk.column.metadata.codec = 2 := codec
  have checked := checkGroup_of_selection picked
    (codec_iff.mpr (.inr (.inr (.inl chosen))))
    (compressedPlainMetadata picked (Leaf.ChunkEncoding.gzipPlainV2_admitsMetadata ..) (advertised _ picked))
    framed counts
  rw [mapped]
  apply finishGroup checked
  apply List.mapM_eq_ok_iff_forall₂.mpr
  rw [← List.zipIdx_map_fst 0 group.frames, List.forall₂_map_left_iff] at physical
  refine physical.imp fun _ _ ⟨_, _, plan, _, verified, decoded, _⟩ => ?_
  have parsed := gzip_plan_parameters plan
  have settings : scalars.pageFor limits.page group.chunk.column.metadata.codec =
      (strict.withFuel limits).page := by
    simp [Limits.pageFor, chosen, fuel, Leaf.Dictionary.Gzip.Limits.withFuel]
  apply decodePage_agrees_plain (advertised _ picked) (by simp [chosen])
  · simpa only [settings] using verified
  · simpa only [chosen] using parsed
  · simpa only [settings] using decoded

private theorem zstdPlain_transfer {scalars : Limits} {strict : Leaf.Zstd.V2.Limits}
    {limits : Leaf.Limits} {bound : Bound} {frame : Parquet.Page.Frame} {ordinal : Nat}
    {raw : List (Option Int64)} (compression : scalars.zstd = strict.compression)
    (read : Leaf.Zstd.V2.decodePage strict limits bound frame ordinal = .ok raw) :
    pageTag frame = some 0 ∧ decodeZstd scalars limits.page bound .plain frame ordinal = .ok raw := by
  unfold Leaf.Zstd.V2.decodePage at read
  cases pageKind : frame.value.kind with
  | dataV2 header =>
    simp only [pageKind] at read
    obtain ⟨status, verified, read⟩ := bind_ok read
    obtain ⟨params, parsed, read⟩ := bind_ok read
    have parsed := mapError_ok parsed
    change Timestamp.Page.parameters bound.binding.leaf bound.levels 6 frame.value = .ok params at parsed
    have body := mapError_ok read
    unfold Leaf.Zstd.V2.decodeBody at body
    obtain ⟨prepared, prep, body⟩ := bind_ok body
    obtain ⟨values, words, restored⟩ := bind_ok body
    have tag : params.encoding = 0 := by
      have ⟨_, layout, valid, _⟩ := FlatColumn.Zstd.prepareFor_sound prep
      by_contra other
      simp [ScalarPage.validateFor, other] at valid
    refine ⟨(parameter_tag parsed).1.trans (congrArg some tag), ?_⟩
    have same : FlatColumn.Zstd.prepareFor 0 (scalars.zstdPage limits.page) params
        (Leaf.Internal.body bound frame) = .ok prepared := by
      rw [Limits.zstdPage, compression]
      exact prep
    simp [decodeZstd, mapError_ok verified, parsed, Encoding.tag, same, decodeZstdValues,
      mapError_ok words, mapError_ok restored, Except.mapError, Bind.bind, Except.bind]
  | dataV1 _ | dictionary _ | skipped _ => simp [pageKind] at read

theorem readGroup_agrees_zstd_v2 {scalars : Limits} {strict : Leaf.Zstd.V2.Limits}
    {limits : Leaf.Limits} {bound : Bound} {index : Nat} {slots : Slots bound}
    (compression : scalars.zstd = strict.compression)
    (advertised : ∀ chunk, Leaf.selectChunkWith .zstdPlainV2 limits bound index = .ok chunk →
      0 ∈ chunk.column.metadata.encodings)
    (accepted : Leaf.Zstd.V2.readGroup strict limits bound index = .ok slots) :
    readGroup scalars limits bound index = .ok slots := by
  unfold Leaf.Zstd.V2.readGroup at accepted
  obtain ⟨group, checked, accepted⟩ := bind_ok accepted
  obtain ⟨pages, decoded, accepted⟩ := bind_ok accepted
  obtain ⟨picked, codec, _, framed, _, _, counts, _, _⟩ := Leaf.Zstd.V2.checkGroup_wire checked
  have chosen : group.chunk.column.metadata.codec = 6 := codec
  have checked := checkGroup_of_selection picked
    (codec_iff.mpr (.inr (.inr (.inr chosen))))
    (compressedPlainMetadata picked (Leaf.ChunkEncoding.zstdPlainV2_admitsMetadata ..) (advertised _ picked))
    framed counts
  have followed : List.Forall₂ (fun (frame, ordinal) raw =>
      decodePage scalars limits.page bound group.chunk.column.metadata.codec
        group.chunk.column.metadata.encodings frame ordinal = .ok raw) group.frames.zipIdx pages :=
    (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun (frame, ordinal) _ read => by
      obtain ⟨tag, exactPage⟩ := zstdPlain_transfer compression read
      have routed : route group.chunk.column.metadata.encodings frame ordinal = .ok .plain :=
        route_ok_iff.mpr ⟨tag, advertised _ picked⟩
      simpa [decodePage, routed, decodeSelected, chosen, Bind.bind, Except.bind] using exactPage
  have sameSlots : pages.flatten.map (Option.map bound.binding.descriptor.decode) = slots :=
    Except.ok.inj accepted
  simpa only [sameSlots] using finishGroup checked (List.mapM_eq_ok_iff_forall₂.mpr followed)

private theorem reference_complete {bound : Bound} {read : Nat → Except Leaf.Error (Slots bound)}
    {indices : List Nat} (ended : (Leaf.Events.referenceGroupsWith read indices).2 = .eos) :
    List.Forall₂ (fun index counts =>
      ∃ slots, read index = .ok slots ∧ counts = slots.map (Option.map Ticks.ticks))
      indices ((Leaf.Events.referenceGroupsWith read indices).1.map (List.map (Option.map Ticks.ticks))) := by
  induction indices with
  | nil => exact .nil
  | cons index rest ih =>
    cases decoded : read index with
    | error cause => simp [Leaf.Events.referenceGroupsWith, decoded] at ended
    | ok slots =>
      simp only [Leaf.Events.referenceGroupsWith, decoded, List.map_cons] at ended ⊢
      exact .cons ⟨slots, decoded, rfl⟩ (ih ended)

private theorem reference_extends {bound : Bound}
    {strict read : Nat → Except Leaf.Error (Slots bound)} {indices : List Nat}
    (compatible : ∀ index slots, strict index = .ok slots → read index = .ok slots)
    (ended : (Leaf.Events.referenceGroupsWith strict indices).2 = .eos) :
    Leaf.Events.referenceGroupsWith read indices = Leaf.Events.referenceGroupsWith strict indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    cases output : strict index with
    | error cause => simp [Leaf.Events.referenceGroupsWith, output] at ended
    | ok slots =>
      simp only [Leaf.Events.referenceGroupsWith, output] at ended
      simp only [Leaf.Events.referenceGroupsWith, output, compatible index slots output, ih ended]

theorem convert_agrees {scalars : Limits} {inputLimits : Leaf.Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {ordinal : Nat} {wire : KBytes}
    {strict : (bound : Bound) → Nat → Except Leaf.Error (Slots bound)}
    (compatible : ∀ bound, Leaf.Events.ToIpc.openBound inputLimits input ordinal = .ok bound →
      ∀ index slots, strict bound index = .ok slots → readGroup scalars inputLimits.leaf bound index = .ok slots)
    (written : Leaf.Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal strict = .ok wire) :
    convert scalars inputLimits outputLimits input ordinal = .ok wire := by
  obtain ⟨bound, opened, ended, _⟩ := Leaf.Events.ToIpc.convertGroups_readback written
  have same := reference_extends (compatible bound opened) ended
  unfold convert
  unfold Leaf.Events.ToIpc.convertGroups Leaf.Events.ToIpc.convertGroupsUsing at written ⊢
  simp only [show Leaf.Events.ToIpc.openBoundWith .modernOnly inputLimits input ordinal = .ok bound from opened,
    Bind.bind, Except.bind] at written ⊢
  rw [Leaf.Events.readBoundWith_reference] at written ⊢
  rw [same]
  exact written

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
          (result.batches.map Arrow.TimestampBatch.Writer.tickCounts) := by
  obtain ⟨bound, opened, ended, result, readback, metadata, exactTicks⟩ :=
    Leaf.Events.ToIpc.convertGroups_readback written
  exact ⟨bound, opened, result, readback, metadata, exactTicks ▸ reference_complete ended⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch
