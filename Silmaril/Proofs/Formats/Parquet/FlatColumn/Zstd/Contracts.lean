module

public import Silmaril.Formats.Parquet.FlatColumn.Zstd.Defs
import Silmaril.Formats.Parquet.FlatColumn.Thms
import Silmaril.Formats.Parquet.Payload.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Silmaril.Formats.Compression.Zstd.CheckedFrame.Huffman.Thms
import Mathlib.Data.List.Forall2
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatColumn.Zstd

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.FlatColumn (Binding pageParameters)
open Silmaril.Formats.Parquet.FlatColumn.Zstd
open Silmaril.Formats.Compression.Zstd

private theorem bind_ok {ε α β : Type} {action : Except ε α} {next : α → Except ε β}
    {out : β} (read : (action >>= next) = .ok out) :
    ∃ value, action = .ok value ∧ next value = .ok out := by
  cases action with
  | error _ => cases read
  | ok value => exact ⟨value, rfl, read⟩

private theorem mapError_ok {ε δ α : Type} {action : Except ε α} {f : ε → δ} {out : α}
    (read : action.mapError f = .ok out) : action = .ok out := by
  cases action with
  | error _ => cases read
  | ok _ => cases read; rfl

theorem decodePayload_sound {limits : CompressionLimits} {bounds : Payload.Bounds} {codec : Int}
    {input output : List UInt8} (read : decodePayload limits bounds codec input = .ok output) :
    PayloadWire limits bounds codec input output := by
  unfold decodePayload at read
  split at read
  · rename_i zero
    subst codec
    obtain ⟨tag, id, wire, inputSize, inputCap, outputSize, outputCap⟩ := Payload.decode_sound (mapError_ok read)
    have tagRaw : tag = .uncompressed := by simpa [Payload.Codec.ofId] using id.symm
    subst tag
    cases wire
    exact ⟨inputSize, inputCap, outputSize, outputCap, .inl ⟨rfl, rfl⟩⟩
  · split at read
    · contradiction
    rename_i isZstd
    have six : codec = 6 := not_not.mp isZstd
    split at read
    · contradiction
    rename_i inputFits
    split at read
    · contradiction
    rename_i outputFits
    split at read
    · contradiction
    rename_i hasLength
    obtain ⟨decoded, decodedFrame, read⟩ := bind_ok read
    obtain ⟨header, wire, _, _, window⟩ := CheckedFrame.Huffman.decode_sound (mapError_ok decodedFrame)
    split at read
    · rename_i extent
      cases read
      have inputSize := Payload.hasLength_iff.mp (by simpa using hasLength)
      exact ⟨inputSize, by omega, extent, by omega, .inr ⟨six, header, wire, window⟩⟩
    · contradiction

private theorem prepare_sound {limits : Limits} {params : ScalarPage.Parameters} {layout : FlatPage.Layout}
    {body : Bytes} {page : ScalarPage.Prepared} (codec : params.codec = 6)
    (read : Internal.prepare limits params layout body = .ok page) :
    PreparedWire limits params layout body page := by
  unfold Internal.prepare at read
  cases version : params.version with
  | v1 definitions repetitions =>
    simp only [version] at read
    split at read
    · contradiction
    rename_i rle
    obtain ⟨decoded, decode, read⟩ := bind_ok read
    obtain ⟨slices, slice, read⟩ := bind_ok read
    obtain ⟨mask, masked, read⟩ := bind_ok read
    cases read
    have wire := decodePayload_sound decode
    simp only [PreparedWire, version]
    exact ⟨by omega, by omega, decoded, slices, codec ▸ wire, mapError_ok slice, mapError_ok masked, rfl⟩
  | v2 nulls rows repetitions definitions flag =>
    simp only [version] at read
    split at read
    · contradiction
    rename_i nullBound
    split at read
    · contradiction
    rename_i rowCount
    obtain ⟨⟨levels, encoded⟩, slice, read⟩ := bind_ok read
    obtain ⟨mask, masked, read⟩ := bind_ok read
    split at read
    · contradiction
    rename_i presentCount
    obtain ⟨decoded, decodedPage, read⟩ := bind_ok read
    cases read
    obtain ⟨rep, hc, hu, _, cap, levelSize, bodyParts⟩ := ScalarPage.splitV2_ok_iff.mp (mapError_ok slice)
    have wire := decodePayload_sound decodedPage
    simp only [PreparedWire, version, Bytes.toList_ofList]
    refine ⟨by omega, by omega, rep, hc, hu, cap, levels, encoded, levelSize, bodyParts, mapError_ok masked,
      not_not.mp presentCount, ?_⟩
    simpa only [codec] using wire

private theorem validate_bounds {encoding : Int} {params : ScalarPage.Parameters} {limits : ScalarPage.Limits} {body : Bytes}
    {layout : FlatPage.Layout} (read : ScalarPage.validateFor encoding params limits body = .ok layout) :
    body.length = params.sizes.compressed ∧ params.sizes.compressed ≤ limits.compressedBytes ∧
      params.sizes.uncompressed ≤ limits.uncompressedBytes := by
  simp only [ScalarPage.validateFor] at read
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  rename_i compressed
  split at read <;> try contradiction
  rename_i uncompressed
  split at read <;> try contradiction
  rename_i size
  exact ⟨not_not.mp size, Nat.le_of_not_gt compressed, Nat.le_of_not_gt uncompressed⟩

theorem prepareFor_sound {encoding : Int} {limits : Limits} {params : ScalarPage.Parameters}
    {body : Bytes} {page : ScalarPage.Prepared} (read : prepareFor encoding limits params body = .ok page) :
    params.codec = 6 ∧ ∃ layout,
      ScalarPage.validateFor encoding params limits.scalar body = .ok layout ∧
      body.length = params.sizes.compressed ∧ params.sizes.compressed ≤ limits.scalar.compressedBytes ∧
      params.sizes.uncompressed ≤ limits.scalar.uncompressedBytes ∧
      PreparedWire limits params layout body page := by
  unfold prepareFor at read
  split at read
  · contradiction
  rename_i rejected
  have codec : params.codec = 6 := not_not.mp rejected
  obtain ⟨layout, valid, prepared⟩ := bind_ok read
  obtain ⟨size, stored, expanded⟩ := validate_bounds (mapError_ok valid)
  exact ⟨codec, layout, mapError_ok valid, size, stored, expanded, prepare_sound codec prepared⟩

private theorem pageParameters_fields {layout : FlatColumn.Layout} {codec : Int} {header : Page.Header}
    {params : ScalarPage.Parameters} (read : pageParameters layout codec header = some params) :
    params.sizes.compressed = header.compressedSize ∧ params.sizes.uncompressed = header.uncompressedSize ∧
      params.codec = codec := by
  cases kind : header.kind <;> simp [pageParameters, kind] at read <;> cases read <;> exact ⟨rfl, rfl, rfl⟩

theorem decodePage_sound {limits : Limits} {layout : FlatColumn.Layout} {leaf : Footer.SchemaElement}
    {metadata : Footer.ColumnMetadata} {header : Page.Header} {body : Bytes} {slots : List (Option Int32)}
    (read : decodePage limits layout leaf metadata header body = .ok slots) :
    PageWire limits layout metadata header body slots := by
  unfold decodePage at read
  split at read
  · contradiction
  rename_i codec
  split at read
  · contradiction
  rename_i params fields
  obtain ⟨levelLayout, validated, read⟩ := bind_ok read
  obtain ⟨page, prepared, read⟩ := bind_ok read
  obtain ⟨values, decoded, read⟩ := bind_ok read
  have codecSix := not_not.mp codec
  obtain ⟨compressed, uncompressed, pageCodec⟩ := pageParameters_fields fields
  have valid := mapError_ok validated
  obtain ⟨size, inputFits, outputFits⟩ := validate_bounds valid
  exact ⟨codecSix, params, levelLayout, page, values, fields, valid, compressed ▸ size,
    compressed ▸ inputFits, uncompressed ▸ outputFits, prepare_sound (pageCodec.trans codecSix) prepared,
    mapError_ok decoded, mapError_ok read⟩

theorem readColumn_wire {snapshot : Snapshot.Checked} {name : String} {layout : FlatColumn.Layout}
    {binding : Binding snapshot ⟨name, .int32, layout⟩} {limits : Limits} {index : Nat} {slots : List (Option Int32)}
    (read : readColumn binding limits index = .ok slots) : ColumnWire binding limits index slots := by
  unfold readColumn at read
  obtain ⟨group, wire⟩ := FlatColumn.readColumnFor_wire read
  obtain ⟨column, chunk, frames, pages, groupAt, columnAt, path, physical, values, codec, span,
    framed, counts, callbacks, ordered, count⟩ := wire
  exact ⟨group, column, chunk, frames, pages, groupAt, columnAt, path, physical, values, codec, span,
    framed, counts, callbacks.imp (fun _ _ h => ⟨decodePage_sound h.1, h.2⟩), ordered, count⟩

end Silmaril.Proofs.Formats.Parquet.FlatColumn.Zstd
