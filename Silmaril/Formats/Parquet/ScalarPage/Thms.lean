module

public import Silmaril.Formats.Parquet.ScalarPage.Defs
import Silmaril.Proofs.Formats.Parquet.ScalarPage.Prepare
import Silmaril.Proofs.Formats.Parquet.ScalarPage.Decode

/-! Exact wire extents and ordered nullable slots for bounded PLAIN data pages. -/

public section

namespace Silmaril.Formats.Parquet.ScalarPage

/-- The raw V2 level prefix fits both size declarations and the input extent. -/
theorem splitV2_ok_iff {sizes : Sizes} {byteLimit repetitionBytes definitionBytes : Nat}
    {source definitions : Bytes} {encoded : List UInt8} :
    splitV2 sizes byteLimit repetitionBytes definitionBytes source = .ok (definitions, encoded) ↔
      repetitionBytes = 0 ∧ definitionBytes ≤ sizes.compressed ∧
      definitionBytes ≤ sizes.uncompressed ∧ source.length = sizes.compressed ∧
      definitionBytes ≤ byteLimit ∧ definitions.length = definitionBytes ∧
      source.toList = definitions.toList ++ encoded :=
  Proofs.Formats.Parquet.ScalarPage.splitV2_ok_iff

/-- Preparation accounts for both byte sizes and the exact checked level and scalar slices. -/
theorem prepare_sound {params : Parameters} {limits : Limits} {source : Bytes}
    {page : Prepared} (h : prepare params limits source = .ok page) :
    ∃ layout, validate params limits source = .ok layout ∧
      PreparedWire params limits layout source page :=
  Proofs.Formats.Parquet.ScalarPage.prepare_sound h

/-- The physical decoder selects the encoding and receives the same checked page layout. -/
theorem prepareFor_sound {encoding : Int} {params : Parameters} {limits : Limits}
    {source : Bytes} {page : Prepared} (h : prepareFor encoding params limits source = .ok page) :
    ∃ layout, validateFor encoding params limits source = .ok layout ∧
      PreparedWire params limits layout source page :=
  Proofs.Formats.Parquet.ScalarPage.prepareFor_sound h

/-- Check the slot count and the V2 header's present count for any selected physical encoding. -/
theorem preparedFor_counts {encoding : Int} {params : Parameters} {limits : Limits}
    {source : Bytes} {page : Prepared} (h : prepareFor encoding params limits source = .ok page) :
    page.mask.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => page.mask.count true = params.numValues - nulls :=
  Proofs.Formats.Parquet.ScalarPage.preparedFor_counts h

/-- V1 expands the whole body, then accounts for all bytes in its required or optional layout. -/
theorem prepared_v1_slices {params : Parameters} {limits : Limits} {source : Bytes}
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
          body = lengthWord ++ definitions.toList ++ page.scalars.toList :=
  Proofs.Formats.Parquet.ScalarPage.prepared_v1_slices version h

/-- A checked GZIP V1 body consumes one exact member with the declared output size. -/
theorem prepared_v1_gzip_member {params : Parameters} {limits : Limits} {layout : FlatPage.Layout}
    {source : Bytes} {page : Prepared} {definitionEncoding repetitionEncoding : Int}
    (version : params.version = .v1 definitionEncoding repetitionEncoding)
    (codec : params.codec = Payload.Codec.gzip.id)
    (wire : PreparedWire params limits layout source page) :
    ∃ expanded, Compression.Gzip.decoder source.toList = some (expanded, []) ∧
      expanded.length = params.sizes.uncompressed :=
  Proofs.Formats.Parquet.ScalarPage.prepared_v1_gzip_member version codec wire

/-- The original V2 flag selects one GZIP member or exact raw suffix bytes. -/
theorem exactPayload_gzip_v2 {compressed uncompressed : Nat} {isCompressed : Bool}
    {stored decoded : List UInt8}
    (wire : ExactPayload compressed uncompressed (v2Codec Payload.Codec.gzip.id (some isCompressed)) stored decoded) :
    stored.length = compressed ∧ decoded.length = uncompressed ∧
      (if isCompressed then Compression.Gzip.decoder stored = some (decoded, []) else stored = decoded) :=
  Proofs.Formats.Parquet.ScalarPage.exactPayload_gzip_v2 wire

theorem prepared_mask_length {params : Parameters} {limits : Limits} {source : Bytes}
    {page : Prepared} (h : prepare params limits source = .ok page) :
    page.mask.length = params.numValues :=
  Proofs.Formats.Parquet.ScalarPage.prepared_mask_length h

theorem readPlain_size {kind : Kind} {count : Nat} {source : Bytes}
    {values : List kind.Value} (h : kind.readPlain count source = .ok values) :
    source.length = kind.plainByteCount count values :=
  Proofs.Formats.Parquet.ScalarPage.readPlain_size h

/-- The output reconstructs the checked definition mask and the PLAIN values in wire order. -/
theorem decode_sound {kind : Kind} {params : Parameters} {limits : Limits} {source : Bytes}
    {output : List (Option kind.Value)} (h : decode kind params limits source = .ok output) :
    ∃ page values, prepare params limits source = .ok page ∧
      kind.readPlain (page.mask.count true) page.scalars = .ok values ∧
      output.map Option.isSome = page.mask ∧ output.filterMap id = values ∧
      values.length = page.mask.count true ∧
      page.scalars.length = kind.plainByteCount (page.mask.count true) values :=
  Proofs.Formats.Parquet.ScalarPage.decode_sound h

theorem decode_counts {kind : Kind} {params : Parameters} {limits : Limits} {source : Bytes}
    {output : List (Option kind.Value)} (h : decode kind params limits source = .ok output) :
    output.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (output.filterMap id).length = params.numValues - nulls :=
  Proofs.Formats.Parquet.ScalarPage.decode_counts h

end Silmaril.Formats.Parquet.ScalarPage
