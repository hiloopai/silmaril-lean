module

public import Silmaril.Formats.Parquet.ScalarPage.Defs
import Silmaril.Formats.Parquet.Payload.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.ScalarPage

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.ScalarPage

public theorem splitV2_ok_iff {sizes : Sizes} {byteLimit repetitionBytes definitionBytes : Nat}
    {source definitions : Bytes} {encoded : List UInt8} :
    splitV2 sizes byteLimit repetitionBytes definitionBytes source = .ok (definitions, encoded) ↔
      repetitionBytes = 0 ∧ definitionBytes ≤ sizes.compressed ∧
      definitionBytes ≤ sizes.uncompressed ∧ source.length = sizes.compressed ∧
      definitionBytes ≤ byteLimit ∧ definitions.length = definitionBytes ∧
      source.toList = definitions.toList ++ encoded := by
  constructor
  · intro h
    simp only [splitV2] at h
    split at h
    · contradiction
    · rename_i rep
      split at h
      · contradiction
      · rename_i extent
        split at h
        · contradiction
        · rename_i sized
          split at h
          · contradiction
          · rename_i cap
            cases h
            have fits : (source.toList.take definitionBytes).length = definitionBytes := by
              simp only [List.length_take, Bytes.length_toList]
              omega
            refine ⟨by omega, by omega, by omega, by omega, by omega, by simpa using fits, ?_⟩
            simp only [Bytes.toList_ofList, List.take_append_drop]
  · rintro ⟨rfl, hc, hu, inputSize, cap, levelSize, bytes⟩
    have extent : ¬ (sizes.compressed < definitionBytes ∨ sizes.uncompressed < definitionBytes) := by
      omega
    have hlen : definitions.toList.length = definitionBytes := by simpa using levelSize
    simp [splitV2, extent, inputSize, Nat.not_lt_of_ge cap, bytes, List.take_left' hlen,
      List.drop_left' hlen]

public theorem bind_ok {ε α β : Type} {action : Except ε α} {next : α → Except ε β}
    {out : β} (h : (action >>= next) = .ok out) :
    ∃ input, action = .ok input ∧ next input = .ok out := by
  cases action with
  | error error => cases h
  | ok value => exact ⟨value, rfl, h⟩

public theorem mapError_ok {ε δ α : Type} {action : Except ε α} {f : ε → δ} {out : α}
    (h : action.mapError f = .ok out) : action = .ok out := by
  cases action with
  | error error => cases h
  | ok value =>
    cases h
    rfl

private theorem exactPayload {limits : Limits} {sizes : Sizes} {levelBytes : Nat}
    {codecId : Int} {input output : List UInt8}
    (h : Payload.decode (limits.payloadBounds sizes levelBytes) codecId input = .ok output) :
    ExactPayload (sizes.compressed - levelBytes) (sizes.uncompressed - levelBytes)
      codecId input output := by
  obtain ⟨codec, id, relation, hin, _, hout, _⟩ := Payload.decode_sound h
  exact ⟨hin, hout, codec, id, relation⟩

private theorem prepareV1_sound {params : Parameters} {limits : Limits} {layout : FlatPage.Layout}
    {definitionEncoding repetitionEncoding : Int} {source : Bytes} {page : Prepared}
    (version : params.version = .v1 definitionEncoding repetitionEncoding)
    (h : prepareV1 params limits layout definitionEncoding repetitionEncoding source = .ok page) :
    PreparedWire params limits layout source page := by
  unfold prepareV1 at h
  split at h
  · contradiction
  · rename_i rle
    obtain ⟨body, hp, h⟩ := bind_ok h
    obtain ⟨sections, hs, h⟩ := bind_ok h
    obtain ⟨mask, hm, h⟩ := bind_ok h
    have payload := exactPayload (mapError_ok hp)
    cases h
    simp only [PreparedWire, version]
    refine ⟨by omega, by omega, body, sections, ?_, mapError_ok hs, mapError_ok hm, rfl⟩
    simpa using payload

private theorem prepareV2_sound {params : Parameters} {limits : Limits} {layout : FlatPage.Layout}
    {nulls rows repetitionBytes definitionBytes : Nat} {isCompressed : Option Bool}
    {source : Bytes} {page : Prepared}
    (version : params.version = .v2 nulls rows repetitionBytes definitionBytes isCompressed)
    (h : prepareV2 params limits layout nulls rows repetitionBytes definitionBytes isCompressed
      source = .ok page) : PreparedWire params limits layout source page := by
  unfold prepareV2 at h
  split at h
  · contradiction
  · rename_i hnulls
    split at h
    · contradiction
    · rename_i hrows
      obtain ⟨⟨definitions, encoded⟩, hs, h⟩ := bind_ok h
      obtain ⟨mask, hm, h⟩ := bind_ok h
      split at h
      · contradiction
      · rename_i count
        obtain ⟨scalars, hp, h⟩ := bind_ok h
        have payload := exactPayload (mapError_ok hp)
        obtain ⟨hreps, hc, hu, _, cap, hlen, bytes⟩ := splitV2_ok_iff.mp hs
        cases h
        simp only [PreparedWire, version]
        refine ⟨by omega, by omega, hreps, hc, hu, cap, definitions, encoded,
          hlen, bytes, mapError_ok hm, by omega, ?_⟩
        simpa only [Bytes.toList_ofList] using payload

public theorem prepareFor_sound {encoding : Int} {params : Parameters} {limits : Limits}
    {source : Bytes} {page : Prepared} (h : prepareFor encoding params limits source = .ok page) :
    ∃ layout, validateFor encoding params limits source = .ok layout ∧
      PreparedWire params limits layout source page := by
  obtain ⟨layout, fits, h⟩ := bind_ok h
  refine ⟨layout, fits, ?_⟩
  cases version : params.version with
  | v1 definitionEncoding repetitionEncoding =>
    rw [version] at h
    exact prepareV1_sound version h
  | v2 nulls rows repetitionBytes definitionBytes isCompressed =>
    rw [version] at h
    exact prepareV2_sound version h

public theorem prepare_sound {params : Parameters} {limits : Limits} {source : Bytes}
    {page : Prepared} (h : prepare params limits source = .ok page) :
    ∃ layout, validate params limits source = .ok layout ∧
      PreparedWire params limits layout source page :=
  prepareFor_sound h

public theorem prepared_v1_slices {params : Parameters} {limits : Limits} {source : Bytes}
    {page : Prepared} {definitionEncoding repetitionEncoding : Int}
    (version : params.version = .v1 definitionEncoding repetitionEncoding)
    (h : prepare params limits source = .ok page) :
    ∃ layout body definitions,
      validate params limits source = .ok layout ∧
      ExactPayload params.sizes.compressed params.sizes.uncompressed
        params.codec source.toList body ∧
      FlatPage.readMask layout params.numValues limits.levels definitions = .ok page.mask ∧
      match layout with
      | .required => definitions = .empty ∧ body = page.scalars.toList
      | .optional => ∃ lengthWord : List UInt8, lengthWord.length = 4 ∧
          KBytes.leVal lengthWord = definitions.length ∧
          body = lengthWord ++ definitions.toList ++ page.scalars.toList := by
  obtain ⟨layout, valid, wire⟩ := prepare_sound h
  simp only [PreparedWire, version] at wire
  obtain ⟨_, _, body, sections, payload, split, mask, scalars⟩ := wire
  refine ⟨layout, body, sections.definitions, valid, payload, mask, ?_⟩
  rw [scalars]
  cases layout with
  | required =>
    change Except.ok ⟨Bytes.empty, Bytes.ofList body⟩ = .ok sections at split
    cases split
    exact ⟨rfl, by simp⟩
  | optional =>
    obtain ⟨lengthWord, size, declared, _, bytes⟩ := FlatPage.splitV1Optional_ok_iff.mp split
    exact ⟨lengthWord, size, declared, by simpa only [Bytes.toList_ofList] using bytes⟩

public theorem preparedFor_counts {encoding : Int} {params : Parameters} {limits : Limits}
    {source : Bytes} {page : Prepared} (h : prepareFor encoding params limits source = .ok page) :
    page.mask.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => page.mask.count true = params.numValues - nulls := by
  obtain ⟨layout, _, wire⟩ := prepareFor_sound h
  cases version : params.version with
  | v1 =>
    simp only [PreparedWire, version] at wire
    obtain ⟨_, _, _, _, _, _, mask, _⟩ := wire
    exact ⟨FlatPage.readMask_length mask, trivial⟩
  | v2 =>
    simp only [PreparedWire, version] at wire
    obtain ⟨_, _, _, _, _, _, _, _, _, _, mask, count, _⟩ := wire
    exact ⟨FlatPage.readMask_length mask, count⟩

public theorem prepared_mask_length {params : Parameters} {limits : Limits} {source : Bytes}
    {page : Prepared} (h : prepare params limits source = .ok page) :
    page.mask.length = params.numValues :=
  (preparedFor_counts h).1

public theorem prepared_v1_gzip_member {params : Parameters} {limits : Limits} {layout : FlatPage.Layout}
    {source : Bytes} {page : Prepared} {definitionEncoding repetitionEncoding : Int}
    (version : params.version = .v1 definitionEncoding repetitionEncoding)
    (codec : params.codec = Payload.Codec.gzip.id)
    (wire : PreparedWire params limits layout source page) :
    ∃ expanded, Compression.Gzip.decoder source.toList = some (expanded, []) ∧
      expanded.length = params.sizes.uncompressed := by
  simp only [PreparedWire, version] at wire
  obtain ⟨_, _, expanded, _, exactPayload, _, _, _⟩ := wire
  obtain ⟨_, length, actual, matched, expansion⟩ := exactPayload
  rw [codec, Payload.Codec.ofId_id] at matched
  cases matched
  cases expansion with
  | gzip exactMember => exact ⟨expanded, exactMember, length⟩

end Silmaril.Proofs.Formats.Parquet.ScalarPage
