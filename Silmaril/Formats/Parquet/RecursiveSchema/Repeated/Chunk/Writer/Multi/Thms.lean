module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.Pack
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.Readback

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi

@[expose] public section

/-- These are the exact page octets in input order. -/
theorem assemble_ordered (pieces : List Writer.Output) :
    (assemble pieces).toList = (pieces.map (fun piece => piece.wire.toList)).flatten :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.assemble_ordered pieces

/-- The construction certifies the partition, the threaded page state,
and the cumulative extent and limits. -/
theorem serialize_construction {limits : Limits} {input : Input} {packed : Packed}
    (written : serialize limits input = .ok packed) : Construction limits input packed :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.construction written

theorem certify_readback {limits : Limits} {input : Input} {packed : Packed} {output : Output}
    (checked : certify limits input packed = .ok output) : Readback limits input packed output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.readback checked

/-- Recovered classified levels and signed words retain the page partition
and original order within each page. -/
theorem PageAgreement.original {start stop : Cursor} {atoms : List (List Rows.Atom)}
    {pieces : List Writer.Output} {pages : List ObservedPage}
    (agreement : PageAgreement start stop atoms pieces pages) :
    pages.map (·.decoded.levels) = atoms.map (List.map (·.levels)) ∧
      pages.map (·.decoded.words) = atoms.map (List.map (·.word)) :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.original agreement

/-- The strict reader sees the supplied CRC policy on every original page. -/
theorem PageAgreement.checksums {limits : Limits} {input : Input}
    {start stop readStop : Cursor} {atoms : List (List Rows.Atom)}
    {pieces : List Writer.Output} {pages : List ObservedPage}
    (built : PiecesWire limits input start stop atoms pieces)
    (matched : PageAgreement start readStop atoms pieces pages) :
    pages.map (·.frame.value.crc) =
      pieces.map (fun piece =>
        if input.checksum then some (Compression.Checksum.crc32.digest piece.page.body.toList) else none) :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.checksums built matched

/-- Successful native emission has exact ordered construction and strict
readback witnesses for the same carrier. -/
theorem emit_wire {limits : Limits} {input : Input} {output : Output}
    (written : emit limits input = .ok output) :
    ∃ packed, serialize limits input = .ok packed ∧
      Construction limits input packed ∧ Readback limits input packed output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.emit_wire written

/-- The metadata-ready offset identifies the first actual page header. -/
theorem first_data_page {limits : Limits} {input : Input} {output : Output}
    (written : emit limits input = .ok output) :
    ∃ frame, output.frames.head? = some frame ∧ frame.header.start = output.dataPageOffset :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.first_data_page written

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi
