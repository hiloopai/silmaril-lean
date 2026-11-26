module

public import Silmaril.Formats.Arrow.FileReader.Defs
import Silmaril.Proofs.Formats.Arrow.FileReader

@[expose] public section

namespace Silmaril.Formats.Arrow.FileReader

/-- Successful footer framing checks both magic words, the padding and the
actual little-endian signed-length domain and budget. -/
theorem readFooterSpan_verified {limits : Limits} {input : KBytes} {span : FooterSpan input}
    (read : readFooterSpan limits input = .ok span) :
    input.read 0 6 = magic ∧ input.read 6 2 = 0 ∧ input.read (input.len - 6) 6 = magic ∧
      input.read (input.len - 10) 4 = span.length ∧ span.length < 2^31 ∧
      span.length ≤ limits.metadataBytes ∧ 8 ≤ span.start :=
  Proofs.Formats.Arrow.FileReader.readFooterSpan_verified read

theorem FooterSpan.bytes_exact {input : KBytes} (span : FooterSpan input) :
    (input.slice span.start span.length).toList =
      (input.toList.drop span.start).take span.length :=
  Proofs.Formats.Arrow.FileReader.footer_exact span

/-- Each indexed range is aligned and lies between the embedded schema and
the footer. Its extent includes its modern prefix and the declared body. -/
theorem Index.block_range {input : KBytes} (index : Index input)
    {block : FileBlock} (member : block ∈ index.footer.blocks) :
    index.schemaEnd ≤ block.offset ∧ block.offset % 8 = 0 ∧ 8 ≤ block.metadataLength ∧
      block.metadataLength % 8 = 0 ∧ block.bodyLength % 8 = 0 ∧
      block.endOffset ≤ index.span.start :=
  Proofs.Formats.Arrow.FileReader.block_range index.fits member

theorem Index.block_order {input : KBytes} (index : Index input) :
    List.Pairwise (fun earlier later : FileBlock => earlier.endOffset ≤ later.offset)
      index.footer.blocks :=
  Proofs.Formats.Arrow.FileReader.block_order index.fits

/-- Reading a checked index entry selects precisely its declared body window. -/
theorem Index.readBlock_exact {input : KBytes} (index : Index input) (limits : Limits)
    {block : FileBlock} (member : block ∈ index.footer.blocks)
    {frame : BatchFrame index.footer.fields}
    (read : index.readBlock limits block member = .ok frame) :
    readEnvelope limits input block.offset = .ok (.metadata (block.metadataLength - 8)) ∧
      readMessage limits (input.slice (block.offset + 8) (block.metadataLength - 8)) =
        .ok ⟨.recordBatch frame.metadata, block.bodyLength⟩ ∧
      frame.body.len = block.bodyLength ∧ frame.body.toList =
        (input.toList.drop (block.offset + block.metadataLength)).take block.bodyLength :=
  Proofs.Formats.Arrow.FileReader.readBlock_exact index limits member read

/-- Successful materialization has one observation per footer entry in
index order. An independent indexed read gives the same observation. -/
theorem readRows_indexed {limits : ObservationLimits} {input : KBytes} {observed : ObservedFile}
    (read : readRows limits input = .ok observed) :
    ∃ index : Index input, readIndex limits.ipc input = .ok index ∧
      observed.fields = index.footer.fields ∧
      observed.batches.length = index.footer.blocks.length ∧
      ∀ n, index.readRowsAt limits n = .ok observed.batches[n]? :=
  Proofs.Formats.Arrow.FileReader.readRows_indexed read

end Silmaril.Formats.Arrow.FileReader
