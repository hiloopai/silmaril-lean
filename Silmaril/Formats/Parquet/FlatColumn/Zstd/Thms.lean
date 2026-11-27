module

public import Silmaril.Formats.Parquet.FlatColumn.Zstd.Defs
import Silmaril.Proofs.Formats.Parquet.FlatColumn.Zstd.Contracts

public section

namespace Silmaril.Formats.Parquet.FlatColumn.Zstd

/-- Success consumes the exact bounds and expands a checked frame or the
    raw value suffix at the exact expected size. -/
theorem decodePayload_sound {limits : CompressionLimits} {bounds : Payload.Bounds} {codec : Int}
    {input output : List UInt8} (read : decodePayload limits bounds codec input = .ok output) :
    PayloadWire limits bounds codec input output :=
  Proofs.Formats.Parquet.FlatColumn.Zstd.decodePayload_sound read

/-- Preparation for a selected encoding shares the exact Zstandard payload and level contract. -/
theorem prepareFor_sound {encoding : Int} {limits : Limits} {params : ScalarPage.Parameters}
    {body : Bytes} {page : ScalarPage.Prepared} (read : prepareFor encoding limits params body = .ok page) :
    params.codec = 6 ∧ ∃ layout,
      ScalarPage.validateFor encoding params limits.scalar body = .ok layout ∧
      body.length = params.sizes.compressed ∧ params.sizes.compressed ≤ limits.scalar.compressedBytes ∧
      params.sizes.uncompressed ≤ limits.scalar.uncompressedBytes ∧
      PreparedWire limits params layout body page :=
  Proofs.Formats.Parquet.FlatColumn.Zstd.prepareFor_sound read

/-- V1 uses the entire original body. V2 keeps the raw level prefix and
    uses the resolved flag for the suffix, with both declared sizes checked. -/
theorem decodePage_sound {limits : Limits} {layout : FlatColumn.Layout} {leaf : Footer.SchemaElement}
    {metadata : Footer.ColumnMetadata} {header : Page.Header} {body : Bytes} {slots : List (Option Int32)}
    (read : decodePage limits layout leaf metadata header body = .ok slots) :
    PageWire limits layout metadata header body slots :=
  Proofs.Formats.Parquet.FlatColumn.Zstd.decodePage_sound read

/-- The accepted slots come in order from the original selected codec-6
    column of the same snapshot, with exact per-page wire witnesses. -/
theorem readColumn_wire {snapshot : Snapshot.Checked} {name : String} {layout : FlatColumn.Layout}
    {binding : Binding snapshot ⟨name, .int32, layout⟩} {limits : Limits} {index : Nat} {slots : List (Option Int32)}
    (read : readColumn binding limits index = .ok slots) : ColumnWire binding limits index slots :=
  Proofs.Formats.Parquet.FlatColumn.Zstd.readColumn_wire read

end Silmaril.Formats.Parquet.FlatColumn.Zstd
