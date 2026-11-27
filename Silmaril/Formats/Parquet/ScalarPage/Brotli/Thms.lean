module

public import Silmaril.Formats.Parquet.ScalarPage.Brotli.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Proofs.Formats.Parquet.ScalarPage.Brotli.Contracts

public section

namespace Silmaril.Formats.Parquet.ScalarPage.Brotli

open Silmaril.Formats.Compression

/-- A compressed slice consumes exactly its stored bytes and regenerates its declared size. -/
theorem decodePayload_sound {limits : Limits} {bounds : Payload.Bounds} {input output : List UInt8}
    (read : Internal.decodePayload limits bounds input = .ok output) : PayloadWire limits bounds input output :=
  Proofs.Formats.Parquet.ScalarPage.Brotli.decodePayload_sound read

/-- Once the slice and caps pass, stream failures retain their cause or the declared-size mismatch. -/
theorem decodePayload_stream_error {limits : Limits} {bounds : Payload.Bounds} {input : List UInt8}
    {error : Brotli.Stream.DistanceSwitch.Error} (inputFits : bounds.compressedSize ≤ bounds.compressedLimit)
    (outputFits : bounds.expectedSize ≤ bounds.outputLimit) (extent : input.length = bounds.compressedSize)
    (decoded : Brotli.Stream.Dictionary.decode (streamLimits limits bounds) input = .error error) :
    Internal.decodePayload limits bounds input = .error (Internal.streamError error) :=
  Proofs.Formats.Parquet.ScalarPage.Brotli.decodePayload_stream_error inputFits outputFits extent decoded

/-- V1 expands the whole body. V2 keeps the original levels and dispatches only the value suffix. -/
theorem expand_sound {limits : Limits} {params : ScalarPage.Parameters} {stored : Bytes} {expanded : List UInt8}
    (read : Internal.expand limits params stored = .ok expanded) : ExpansionWire limits params stored expanded :=
  Proofs.Formats.Parquet.ScalarPage.Brotli.expand_sound read

/-- The checked header, stored slice and CRC come from the same immutable source. -/
theorem decodeAt_sound {limits : Limits} {layout : FlatColumn.Layout} {codec : Int}
    {source : Bytes} {chunk : Footer.Span} {cursor : Nat} {result : Result}
    (read : decodeAt limits layout codec source chunk cursor = .ok result) :
    Wire limits layout codec source chunk cursor result :=
  Proofs.Formats.Parquet.ScalarPage.Brotli.decodeAt_sound read

/-- A failed checksum stops data-page preparation and payload decoding. -/
theorem decodeAt_checksum_error {limits : Limits} {layout : FlatColumn.Layout} {codec : Int}
    {source : Bytes} {chunk : Footer.Span} {cursor : Nat} {frame : Page.Frame} {reason : Page.Checksum.Error}
    (admitted : codec = Payload.Codec.brotli.id)
    (framed : Page.readPage limits.framing source chunk cursor = .ok frame)
    (failed : Page.Checksum.verify limits.page.compressedBytes source frame = .error reason) :
    decodeAt limits layout codec source chunk cursor = .error (.checksum reason) :=
  Proofs.Formats.Parquet.ScalarPage.Brotli.decodeAt_checksum_error admitted framed failed

/-- A declared CRC matches IEEE CRC-32 over the exact stored body, including V2 levels. -/
theorem Wire.crc {limits : Limits} {layout : FlatColumn.Layout} {codec : Int}
    {source : Bytes} {chunk : Footer.Span} {cursor : Nat} {result : Result}
    (wire : Wire limits layout codec source chunk cursor result) :
    match result.checksum with
    | .absent => result.frame.value.crc = none
    | .valid value => result.frame.value.crc = some value ∧
      Compression.crc32Spec (Page.Checksum.payloadBytes source result.frame).toList = value :=
  Proofs.Formats.Parquet.ScalarPage.Brotli.Wire.crc wire

end Silmaril.Formats.Parquet.ScalarPage.Brotli
