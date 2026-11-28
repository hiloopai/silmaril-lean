module

public import Silmaril.Formats.Parquet.Page.Defs
import Silmaril.Proofs.Formats.Parquet.Page.Prefix
import Silmaril.Proofs.Formats.Parquet.Page.Contracts

/-! Exact header consumption and checked column-chunk spans. -/

public section

namespace Silmaril.Formats.Parquet.Page

/-- The prefix reader ends immediately after an in-window STOP. -/
theorem readHeaderPrefix_stop {limits : HeaderLimits} {window : Bytes} {header : Header}
    {consumed : Nat} (parsed : readHeaderPrefix limits window = .ok (header, consumed)) :
    0 < consumed ∧ consumed ≤ window.length ∧ window.data[consumed - 1]? = some 0 :=
  Proofs.Formats.Parquet.Page.readHeaderPrefix_stop parsed

/-- A page makes positive cursor progress and its payload fits the source and chunk. -/
theorem readPage_within {limits : Limits} {source : Bytes} {chunk : Footer.Span}
    {cursor : Nat} {frame : Frame} (parsed : readPage limits source chunk cursor = .ok frame) :
    FrameWithin chunk cursor frame ∧ chunk.stop ≤ source.length :=
  Proofs.Formats.Parquet.Page.readPage_within parsed

/-- The header denotes exactly the checked source slice starting at the cursor
and ending immediately after the STOP consumed by the typed reader. -/
theorem readPage_exactPrefix {limits : Limits} {source : Bytes} {chunk : Footer.Span}
    {cursor : Nat} {frame : Frame} (parsed : readPage limits source chunk cursor = .ok frame) :
    ∃ bytes consumed,
      source.slice? cursor (some frame.header.stop) = some bytes ∧
      bytes.length = consumed ∧ frame.header.stop = cursor + consumed ∧
      consumed ≤ limits.maxHeaderBytes ∧ source.data[frame.header.stop - 1]? = some 0 ∧
      readHeaderPrefix limits.header (Footer.fileBytes source cursor (headerWindowStop limits chunk cursor)) =
        .ok (frame.value, consumed) :=
  Proofs.Formats.Parquet.Page.readPage_exactPrefix parsed

/-- A successful scan covers the entire chunk in wire order with adjacent frames. -/
theorem readChunk_chain {limits : Limits} {source : Bytes} {chunk : Footer.Span}
    {frames : List Frame} (parsed : readChunk limits source chunk = .ok frames) :
    chunk.start ≤ chunk.stop ∧ chunk.stop ≤ source.length ∧ Chain chunk chunk.start chunk.stop frames :=
  Proofs.Formats.Parquet.Page.readChunk_chain parsed

/-- Each chunk frame is the original page parse at its absolute header cursor. -/
theorem readChunk_readPage {limits : Limits} {source : Bytes} {chunk : Footer.Span}
    {frames : List Frame} (parsed : readChunk limits source chunk = .ok frames) :
    ∀ frame ∈ frames, readPage limits source chunk frame.header.start = .ok frame :=
  Proofs.Formats.Parquet.Page.readChunk_readPage parsed

/-- A previous payload ends at or before every subsequent header. -/
theorem readChunk_payloads_disjoint {limits : Limits} {source : Bytes} {chunk : Footer.Span}
    {frames : List Frame} (parsed : readChunk limits source chunk = .ok frames) :
    frames.Pairwise (fun first second => first.payload.stop ≤ second.header.start) :=
  Proofs.Formats.Parquet.Page.readChunk_payloads_disjoint parsed

/-- Every payload in a successful scan lies inside the declared chunk. -/
theorem readChunk_payloads_bounded {limits : Limits} {source : Bytes} {chunk : Footer.Span}
    {frames : List Frame} (parsed : readChunk limits source chunk = .ok frames) :
    ∀ frame ∈ frames, FrameWithin chunk frame.header.start frame :=
  Proofs.Formats.Parquet.Page.readChunk_payloads_bounded parsed

/-- The V2 sections partition the payload in wire order. -/
theorem v2Spans_bounds {frame : Frame} {spans : V2Spans} (split : frame.v2Spans = some spans) :
    spans.repetition.start = frame.payload.start ∧
    spans.repetition.start ≤ spans.repetition.stop ∧ spans.repetition.stop = spans.definition.start ∧
    spans.definition.start ≤ spans.definition.stop ∧ spans.definition.stop = spans.values.start ∧
    spans.values.start ≤ spans.values.stop ∧ spans.values.stop = frame.payload.stop :=
  Proofs.Formats.Parquet.Page.v2Spans_bounds split

end Silmaril.Formats.Parquet.Page
