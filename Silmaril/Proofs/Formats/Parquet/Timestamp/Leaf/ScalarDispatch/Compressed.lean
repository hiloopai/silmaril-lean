module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Defs
import Silmaril.Formats.Parquet.Timestamp.Page.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound)
open Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch

private theorem gzip_prepared {scalars : Limits} {limits : ScalarPage.Limits} {bound : Bound}
    {declared : List Int} {frame : Parquet.Page.Frame} {slots : List (Option Int64)}
    (wire : PageWire scalars limits bound 2 declared frame slots) :
    ∃ (params : ScalarPage.Parameters) (layout : FlatPage.Layout) (prepared : ScalarPage.Prepared),
      Timestamp.Page.parameters bound.binding.leaf bound.levels 2 frame.value = .ok params ∧
      ScalarPage.PreparedWire params (scalars.pageFor limits 2) layout (Leaf.Internal.body bound frame) prepared ∧
      slots.map Option.isSome = prepared.mask := by
  obtain ⟨_, encoding, _, _, branch⟩ := wire
  cases encoding with
  | plain =>
    obtain ⟨_, params, layout, prepared, _, _, _, _, _, _, parsed, _, _, exactBody, _, mask, _⟩ := branch
    exact ⟨params, layout, prepared, parsed, exactBody, mask⟩
  | delta =>
    obtain ⟨_, params, layout, prepared, _, _, _, _, _, _, parsed, _, _, exactBody,
      _, _, _, mask, _, _, _⟩ := branch
    exact ⟨params, layout, prepared, parsed, exactBody, mask⟩
  | split =>
    obtain ⟨_, params, layout, prepared, _, _, _, _, _, _, parsed, _, _, exactBody,
      _, _, mask, _, _, _⟩ := branch
    exact ⟨params, layout, prepared, parsed, exactBody, mask⟩

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
      | _ => False := by
  obtain ⟨params, layout, prepared, parsed, physics, mask⟩ := gzip_prepared wire
  obtain ⟨_, _, codec, sizes, header⟩ := Timestamp.Page.parameters_sound parsed
  refine ⟨prepared, layout, mask, ?_⟩
  cases kind : frame.value.kind with
  | dataV1 info =>
    simp only [kind] at header
    obtain ⟨count, _, version⟩ := header
    rw [ScalarPage.PreparedWire, version, sizes, codec, count] at physics
    obtain ⟨_, _, body, sections, ⟨storedLength, outputLength, decodeCodec, chosen, exactBody⟩, split, levels, values⟩ :=
      physics
    have selected : decodeCodec = .gzip := (Option.some.inj chosen).symm
    subst decodeCodec
    cases exactBody with
    | gzip member => exact ⟨body, sections, by simpa using storedLength, outputLength, member, split, levels, values⟩
  | dataV2 info =>
    simp only [kind] at header
    obtain ⟨count, _, version⟩ := header
    rw [ScalarPage.PreparedWire, version, sizes, codec, count] at physics
    obtain ⟨_, _, repetitions, storedFits, expandedFits, _, definitions, suffix, length, split, levels, count, extent⟩ :=
      physics
    obtain ⟨storedLength, expandedLength, exactSuffix⟩ := ScalarPage.exactPayload_gzip_v2 extent
    exact ⟨repetitions, storedFits, expandedFits, definitions, suffix, length, split, levels,
      count, storedLength, by simpa using expandedLength, exactSuffix⟩
  | dictionary _ | skipped _ => simp only [kind] at header

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
      | _ => False := by
  obtain ⟨_, params, layout, prepared, values, _, _, _, _, _, _, parsed, _, _, physics, scalar, mask, ordered⟩ := wire
  obtain ⟨_, _, _, sizes, header⟩ := Timestamp.Page.parameters_sound parsed
  refine ⟨prepared, layout, values, scalar, mask, ordered, ?_⟩
  cases kind : frame.value.kind with
  | dataV1 info =>
    simp only [kind] at header
    obtain ⟨count, _, version⟩ := header
    rw [FlatColumn.Zstd.PreparedWire, version, sizes, count] at physics
    obtain ⟨_, _, expanded, slices, extent, split, levels, values⟩ := physics
    exact ⟨expanded, slices, extent, split, levels, values⟩
  | dataV2 info =>
    simp only [kind] at header
    obtain ⟨count, _, version⟩ := header
    rw [FlatColumn.Zstd.PreparedWire, version, sizes, count] at physics
    obtain ⟨_, _, repetitions, storedFits, expandedFits, _, definitions, suffix, length, split, levels, count, extent⟩ :=
      physics
    exact ⟨repetitions, storedFits, expandedFits, definitions, suffix, length, split, levels, count, extent⟩
  | dictionary _ | skipped _ => simp only [kind] at header

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.ScalarDispatch
