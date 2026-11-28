module

public import Silmaril.Formats.Parquet.Page.Defs
import Silmaril.Proofs.Formats.Parquet.Page.Prefix
import Init.Data.ByteArray.Lemmas
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.Page

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Page

private theorem readPage_model {limits : Limits} {source : Bytes} {chunk : Footer.Span}
    {cursor : Nat} {frame : Frame} (parsed : readPage limits source chunk cursor = .ok frame) :
    FrameWithin chunk cursor frame ∧ chunk.stop ≤ source.length ∧
      ∃ consumed, frame.header.stop = cursor + consumed ∧
        readHeaderPrefix limits.header (Footer.fileBytes source cursor (headerWindowStop limits chunk cursor)) =
          .ok (frame.value, consumed) := by
  by_cases valid : chunk.start ≤ cursor ∧ cursor < chunk.stop ∧ chunk.stop ≤ source.length
  · cases wire : readHeaderPrefix limits.header
      (Footer.fileBytes source cursor (headerWindowStop limits chunk cursor)) with
    | error e => simp [readPage, valid, wire, Except.mapError,
        bind, Except.bind] at parsed
    | ok result =>
      obtain ⟨value, consumed⟩ := result
      by_cases bounded : chunk.stop < cursor + consumed + value.compressedSize
      · simp [readPage, valid, wire, bounded, Except.mapError,
          bind, Except.bind] at parsed
      · simp [readPage, valid, wire, bounded, Except.mapError,
          bind, Except.bind, pure, Except.pure] at parsed
        subst frame
        have progress := (readHeaderPrefix_stop wire).1
        exact ⟨⟨valid.1, rfl, by change cursor < cursor + consumed; omega, rfl, rfl, by
          change cursor + consumed + value.compressedSize ≤ chunk.stop; omega⟩,
          valid.2.2, consumed, rfl, rfl⟩
  · simp [readPage, valid, bind, Except.bind] at parsed

public theorem readPage_within {limits : Limits} {source : Bytes} {chunk : Footer.Span}
    {cursor : Nat} {frame : Frame} (parsed : readPage limits source chunk cursor = .ok frame) :
    FrameWithin chunk cursor frame ∧ chunk.stop ≤ source.length :=
  ⟨(readPage_model parsed).1, (readPage_model parsed).2.1⟩

public theorem readPage_exactPrefix {limits : Limits} {source : Bytes} {chunk : Footer.Span}
    {cursor : Nat} {frame : Frame} (parsed : readPage limits source chunk cursor = .ok frame) :
    ∃ bytes consumed,
      source.slice? cursor (some frame.header.stop) = some bytes ∧
      bytes.length = consumed ∧ frame.header.stop = cursor + consumed ∧
      consumed ≤ limits.maxHeaderBytes ∧ source.data[frame.header.stop - 1]? = some 0 ∧
      readHeaderPrefix limits.header (Footer.fileBytes source cursor (headerWindowStop limits chunk cursor)) =
        .ok (frame.value, consumed) := by
  obtain ⟨within, fileBound, consumed, endOffset, wire⟩ := readPage_model parsed
  let stop := headerWindowStop limits chunk cursor
  have stopBound : stop ≤ source.length := Nat.le_trans (Nat.min_le_left _ _) fileBound
  have cap : stop ≤ cursor + limits.maxHeaderBytes := Nat.min_le_right _ _
  have length : (Footer.fileBytes source cursor stop).length = stop - cursor := by
    change stop ≤ source.data.size at stopBound
    simp [Footer.fileBytes, Bytes.length, Nat.min_eq_left stopBound]
  obtain ⟨positive, consumedBound, zeroAt⟩ := readHeaderPrefix_stop wire
  change consumed ≤ (Footer.fileBytes source cursor stop).length at consumedBound
  rw [length] at consumedBound
  have headerBound : frame.header.stop ≤ source.length := by omega
  have sliced : source.slice? cursor (some frame.header.stop) =
      some (Footer.fileBytes source cursor frame.header.stop) := by
    apply Bytes.slice?_eq_some_iff.mpr
    refine ⟨by simp [endOffset], headerBound, Bytes.ext ?_⟩
    rw [Bytes.toList_ofList]
    simp [Footer.fileBytes, Bytes.toList, ByteArray.data_extract]
  have terminal : source.data[frame.header.stop - 1]? = some 0 := by
    change (source.data.extract cursor stop)[consumed - 1]? = some 0 at zeroAt
    have withinSlice : consumed - 1 < (source.data.extract cursor stop).size := by
      change consumed - 1 < (Footer.fileBytes source cursor stop).length
      omega
    have withinFile : frame.header.stop - 1 < source.data.size := by
      change frame.header.stop - 1 < source.length
      omega
    rw [getElem?_pos (source.data.extract cursor stop) (consumed - 1) withinSlice,
      ByteArray.getElem_extract] at zeroAt
    rw [getElem?_pos source.data (frame.header.stop - 1) withinFile]
    have offset : frame.header.stop - 1 = cursor + (consumed - 1) := by omega
    exact (congrArg some (getElem_congr_idx (c := source.data) (w := withinFile) offset)).trans zeroAt
  exact ⟨_, consumed, sliced, by simpa [endOffset] using Bytes.length_of_slice? sliced,
    endOffset, by omega, terminal, wire⟩

private theorem chain_append {chunk : Footer.Span} {start cursor : Nat} {frames : List Frame}
    (chain : Chain chunk start cursor frames) {frame : Frame} (within : FrameWithin chunk cursor frame) :
    Chain chunk start frame.payload.stop (frames ++ [frame]) := by
  induction chain with
  | nil _ => exact .cons within (.nil _)
  | cons first rest ih => exact .cons first (ih within)

public theorem readChunk_chain {limits : Limits} {source : Bytes} {chunk : Footer.Span}
    {frames : List Frame} (parsed : readChunk limits source chunk = .ok frames) :
    chunk.start ≤ chunk.stop ∧ chunk.stop ≤ source.length ∧ Chain chunk chunk.start chunk.stop frames := by
  have go (budget cursor : Nat) (reversed : List Frame)
      (chain : Chain chunk chunk.start cursor reversed.reverse)
      (parsed : readChunk.go limits source chunk budget cursor reversed = .ok frames) :
      Chain chunk chunk.start chunk.stop frames := by
    induction budget generalizing cursor reversed with
    | zero =>
      by_cases last : cursor = chunk.stop
      · simp [readChunk.go, last] at parsed
        rwa [← last, ← parsed]
      · simp [readChunk.go, last] at parsed
    | succ budget ih =>
      by_cases last : cursor = chunk.stop
      · simp [readChunk.go, last] at parsed
        rwa [← last, ← parsed]
      · cases step : readPage limits source chunk cursor with
        | error e => simp [readChunk.go, last, step] at parsed
        | ok frame =>
          apply ih frame.payload.stop (frame :: reversed)
          · simpa only [List.reverse_cons] using chain_append chain (readPage_within step).1
          · simpa [readChunk.go, last, step] using parsed
  by_cases valid : chunk.start ≤ chunk.stop ∧ chunk.stop ≤ source.length
  · exact ⟨valid.1, valid.2, go limits.maxPages chunk.start [] (.nil _) (by simpa [readChunk, valid] using parsed)⟩
  · simp [readChunk, valid] at parsed

public theorem readChunk_readPage {limits : Limits} {source : Bytes} {chunk : Footer.Span}
    {frames : List Frame} (parsed : readChunk limits source chunk = .ok frames) :
    ∀ frame ∈ frames, readPage limits source chunk frame.header.start = .ok frame := by
  let Bound (frame : Frame) := readPage limits source chunk frame.header.start = .ok frame
  have go (budget cursor : Nat) (reversed : List Frame)
      (prior : ∀ frame ∈ reversed, Bound frame)
      (scan : readChunk.go limits source chunk budget cursor reversed = .ok frames) :
      ∀ frame ∈ frames, Bound frame := by
    induction budget generalizing cursor reversed with
    | zero =>
      by_cases last : cursor = chunk.stop
      · simp [readChunk.go, last] at scan
        simpa [← scan] using prior
      · simp [readChunk.go, last] at scan
    | succ budget ih =>
      by_cases last : cursor = chunk.stop
      · simp [readChunk.go, last] at scan
        simpa [← scan] using prior
      · cases next : readPage limits source chunk cursor with
        | error e => simp [readChunk.go, last, next] at scan
        | ok frame =>
          apply ih frame.payload.stop (frame :: reversed)
          · intro member atFrame
            rcases List.mem_cons.mp atFrame with rfl | rest
            · change readPage limits source chunk member.header.start = .ok member
              rw [(readPage_within next).1.headerStart]
              exact next
            · exact prior member rest
          · simpa [readChunk.go, last, next] using scan
  by_cases valid : chunk.start ≤ chunk.stop ∧ chunk.stop ≤ source.length
  · exact go limits.maxPages chunk.start [] (by simp) (by simpa [readChunk, valid] using parsed)
  · simp [readChunk, valid] at parsed

private theorem chain_lower {chunk : Footer.Span} {start stop : Nat} {frames : List Frame}
    (chain : Chain chunk start stop frames) : ∀ frame ∈ frames, start ≤ frame.header.start := by
  induction chain with
  | nil _ => simp
  | cons within _ ih =>
    simp only [List.mem_cons, forall_eq_or_imp]
    refine ⟨by rw [within.headerStart], fun frame member => ?_⟩
    have lower := ih frame member
    have progress := within.headerProgress
    rw [within.adjacent] at progress
    have size := within.payloadWidth
    omega

private theorem chain_disjoint {chunk : Footer.Span} {start stop : Nat} {frames : List Frame}
    (chain : Chain chunk start stop frames) :
    frames.Pairwise (fun first second => first.payload.stop ≤ second.header.start) := by
  induction chain with
  | nil _ => exact .nil
  | cons _ tail ih => exact .cons (chain_lower tail) ih

public theorem readChunk_payloads_disjoint {limits : Limits} {source : Bytes} {chunk : Footer.Span}
    {frames : List Frame} (parsed : readChunk limits source chunk = .ok frames) :
    frames.Pairwise (fun first second => first.payload.stop ≤ second.header.start) :=
  chain_disjoint (readChunk_chain parsed).2.2

private theorem chain_bounded {chunk : Footer.Span} {start stop : Nat} {frames : List Frame}
    (chain : Chain chunk start stop frames) :
    ∀ frame ∈ frames, FrameWithin chunk frame.header.start frame := by
  induction chain with
  | nil _ => simp
  | cons within _ ih =>
    intro _ member
    rcases List.mem_cons.mp member with rfl | rest
    · rw [within.headerStart]
      exact within
    · exact ih _ rest

public theorem readChunk_payloads_bounded {limits : Limits} {source : Bytes} {chunk : Footer.Span}
    {frames : List Frame} (parsed : readChunk limits source chunk = .ok frames) :
    ∀ frame ∈ frames, FrameWithin chunk frame.header.start frame :=
  chain_bounded (readChunk_chain parsed).2.2

public theorem v2Spans_bounds {frame : Frame} {spans : V2Spans} (split : frame.v2Spans = some spans) :
    spans.repetition.start = frame.payload.start ∧
    spans.repetition.start ≤ spans.repetition.stop ∧ spans.repetition.stop = spans.definition.start ∧
    spans.definition.start ≤ spans.definition.stop ∧ spans.definition.stop = spans.values.start ∧
    spans.values.start ≤ spans.values.stop ∧ spans.values.stop = frame.payload.stop := by
  cases kind : frame.value.kind with
  | dataV2 header =>
    by_cases bounded : frame.payload.start + header.repetitionBytes + header.definitionBytes ≤ frame.payload.stop
    · simp [Frame.v2Spans, kind, bounded] at split
      subst spans
      exact ⟨rfl, Nat.le_add_right _ _, rfl, Nat.le_add_right _ _, rfl, bounded, rfl⟩
    · simp [Frame.v2Spans, kind, bounded] at split
  | dataV1 _ | dictionary _ | skipped _ => simp [Frame.v2Spans, kind] at split

end Silmaril.Proofs.Formats.Parquet.Page
