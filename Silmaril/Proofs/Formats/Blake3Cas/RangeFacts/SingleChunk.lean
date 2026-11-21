module

public import Silmaril.Formats.Blake3Cas.RangeFacts.SingleChunk.Defs
import Init.Data.Vector.OfFn

public section

namespace Silmaril.Proofs.Formats.Blake3Cas.RangeFacts.SingleChunk

open Silmaril.Crypto.Blake3
open Silmaril.Formats
open Silmaril.Formats.Blake3Cas
open Silmaril.Formats.Blake3Cas.RangeFacts
open Silmaril.Formats.Blake3Cas.RangeFacts.SingleChunk

private def span : Bao.Span := ⟨0, 1⟩

private def leafPlan (size : Nat) : Bao.Plan := .leaf span size

private theorem chunks_one {size : Nat} (small : size ≤ 1024) : Bao.chunks size = 1 := by
  unfold Bao.chunks Bao.chunkBytes
  omega

private theorem span_width {size : Nat} (small : size ≤ 1024) : span.byteSize size = size := by
  simp [span, Bao.Span.byteSize, Bao.Span.endChunk, Bao.Span.byteStart, Bao.chunkBytes, Nat.min_eq_left small]

private theorem plan_full {size : Nat} (small : size ≤ 1024) : Bao.fullPlan size 1 = leafPlan size := by
  simp [Bao.fullPlan, Bao.plan, chunks_one small, Bao.planAt, Bao.overlaps, Bao.Span.endChunk,
    leafPlan]
  exact ⟨rfl, span_width small⟩

private theorem plan_slice {size : Nat} (small : size ≤ 1024) (request : Bao.RangeRequest) :
    Bao.slicePlan size request = leafPlan size := by
  have selection : Bao.sliceChunks size request = ⟨0, 1⟩ := by simp [Bao.sliceChunks, chunks_one small]
  simpa [Bao.slicePlan, selection, Bao.fullPlan, chunks_one small] using plan_full small

private theorem parse_loaded {bytes : Bytes} {raw : Bao.Digest} {cv : CV}
    (parsed : Bao.digest? bytes = some raw) (roundTrip : loadWords raw = cv) (wire : digestBytes cv = bytes) :
    parseCV bytes = some ⟨cv, wire⟩ := by
  simp only [parseCV, parsed, Option.bind_eq_bind, Option.bind_some, roundTrip, dite_eq_left wire]

private theorem parse_digest (cv : CV) : parseCV (digestBytes cv) = some ⟨cv, rfl⟩ := by
  let raw := Vector.ofFn (fun pos : Fin 32 => wordByte cv[pos.val / 4] (pos.val % 4))
  have wire : raw.toList = digestBytes cv := rfl
  have parsed : Bao.digest? (digestBytes cv) = some raw := by
    simp only [Bao.digest?, digestBytes_length, dite_true, Option.some.injEq]
    exact Vector.toList_inj.mp (by simp [wire])
  have roundTrip : loadWords raw = cv := by
    apply Vector.ext
    intro index bound
    have atByte (delta : Nat) (small : delta < 4) :
        raw[4 * index + delta]'(by omega) = wordByte cv[index] delta := by
      simp [raw, show (4 * index + delta) / 4 = index by omega,
        show (4 * index + delta) % 4 = delta by omega]
    simp only [loadWords, Vector.getElem_ofFn]
    have zero : raw[4 * index] = wordByte cv[index] 0 := by simpa only [Nat.add_zero] using atByte 0 (by decide)
    calc
      _ = packWord (wordByte cv[index] 0) (wordByte cv[index] 1) (wordByte cv[index] 2)
          (wordByte cv[index] 3) := by simp only [zero, atByte 1 (by decide), atByte 2 (by decide), atByte 3 (by decide)]
      _ = cv[index] := by simpa only [wordByte] using Silmaril.Crypto.Word.pack32LE_unpack32LE cv[index]
  exact parse_loaded parsed roundTrip rfl

private def leafBody {digest bytes : Bytes} {cv : CV} (small : bytes.length ≤ 1024)
    (valid : validSize bytes.length) (digestEq : digestBytes cv = digest)
    (hit : subtreeCV? true (geometry 0 bytes.length) bytes = some cv) :
    CompleteBody bytes.length digest [bytes] :=
  let anchor := rootAnchor valid digestEq
  let aligned : Aligned span (geometry 0 bytes.length) 0 := ⟨by rw [canonicalSpan, chunks_one small]; rfl, rfl⟩
  let width : bytes.length = (geometry 0 bytes.length).size := (geometry_size ..).symm
  let facts := anchor.openCell width hit
  ⟨.cons (.data span ⟨0, bytes, facts.1⟩ ⟨_, true, cv, true, aligned, (span_width small).symm,
      width, anchor, hit⟩) .nil, ⟨[], some ⟨facts.2 rfl⟩⟩, rfl⟩

private theorem check_leaf {digest bytes : Bytes} {cap : Nat} {cv : CV}
    (small : bytes.length ≤ 1024) (withinCap : bytes.length ≤ cap) (valid : validSize bytes.length)
    (digestEq : digestBytes cv = digest)
    (hit : subtreeCV? true (geometry 0 bytes.length) bytes = some cv) :
    checkBody? bytes.length cap digest (leafPlan bytes.length) [bytes] = some (leafBody small valid digestEq hit) := by
  subst digest
  have aligned : Aligned span (geometry 0 bytes.length) 0 := ⟨by rw [canonicalSpan, chunks_one small]; rfl, rfl⟩
  simp [checkBody?, begin?, Nat.not_lt.mpr withinCap, valid, parse_digest, leafPlan, checkTape?, step?,
    aligned, span_width small, geometry_size, hit, leafBody]

private theorem bytes_cast {size start before after : Nat} {digest : Bytes}
    (same : before = after) (coverage : Coverage size digest start before) :
    (same ▸ coverage : Coverage size digest start after).bytes = coverage.bytes := by cases same; rfl

private theorem range_leaf {digest bytes : Bytes} {cv : CV} (window : Bao.RangeRequest)
    (small : bytes.length ≤ 1024) (valid : validSize bytes.length) (digestEq : digestBytes cv = digest)
    (hit : subtreeCV? true (geometry 0 bytes.length) bytes = some cv)
    (bound : window.start + window.count ≤ bytes.length) :
    ∃ range, (leafBody small valid digestEq hit).range? window = some range ∧
      range.coverage.bytes = (bytes.drop window.start).take window.count := by
  have taken : ((bytes.drop window.start).take window.count).length = window.count := by
    simp [List.length_take]; omega
  by_cases empty : window.count = 0
  · have atStart : window.start ≤ bytes.length := by omega
    simp [CompleteBody.range?, leafBody, Tape.project?, Cell.project?, project?, empty,
      atStart, bytes_cast, Coverage.bytes, Advance.bytes]
  · have nonempty : window.start < window.start + window.count := by omega
    simp [CompleteBody.range?, leafBody, Tape.project?, Cell.project?, project?, bound,
      nonempty, taken, Nat.pos_of_ne_zero empty, bytes_cast, Coverage.bytes, Advance.bytes]

private theorem ofBody_projected {size : Nat} {digest : Bytes} {fields : List Bytes} {request : Request}
    {body : CompleteBody size digest fields} {range : ExactRange size digest (request.window size)}
    (projected : body.range? (request.window size) = some range) :
    ofBody? body request = some ⟨size, .body body projected, body.final.eof⟩ := by
  unfold ofBody?
  split
  · rename_i failed; exact nomatch projected.symm.trans failed
  · rename_i got success
    have same : got = range := Option.some.inj (success.symm.trans projected)
    cases same
    rfl

private theorem project_leaf {digest bytes : Bytes} {cv : CV} {request : Request}
    (small : bytes.length ≤ 1024) (valid : validSize bytes.length) (digestEq : digestBytes cv = digest)
    (hit : subtreeCV? true (geometry 0 bytes.length) bytes = some cv)
    (bound : let window := request.window bytes.length; window.start + window.count ≤ bytes.length) :
    ∃ response, ofBody? (leafBody small valid digestEq hit) request = some response ∧
      response.claim = bytes.length ∧ response.eof.isSome = true ∧
      response.done.bytes = (bytes.drop (request.window bytes.length).start).take (request.window bytes.length).count := by
  obtain ⟨range, projected, data⟩ := range_leaf (request.window bytes.length) small valid digestEq hit bound
  exact ⟨_, ofBody_projected projected, rfl, rfl, data⟩

theorem complete {digest original : Bytes} (profile : Profile) (request : Request) {cap : Nat}
    (named : Named concrete digest original) (small : original.length ≤ 1024) (withinCap : original.length ≤ cap)
    (bound : let window := request.window original.length; window.start + window.count ≤ original.length) :
    ∃ wire response, encode? profile request original = some wire ∧
      decode? profile cap digest request wire original = some response ∧
      response.claim = original.length ∧ response.eof.isSome = true ∧
      response.done.bytes = (original.drop (request.window original.length).start).take (request.window original.length).count := by
  obtain ⟨valid, cv, trace, digestEq⟩ := named
  have hit : subtreeCV? true (geometry 0 original.length) original = some cv := eval_graph.mpr trace
  obtain ⟨response, project, claim, eof, data⟩ := project_leaf small valid digestEq hit bound
  have validWire : original.length < Bao.u64Limit := valid
  have check := check_leaf small withinCap valid digestEq hit
  have full := plan_full small
  let window := request.window original.length
  have windowEq : request.window original.length = window := rfl
  have slice := plan_slice small window
  have windowValid : window.valid = true := by
    change window.start + window.count ≤ original.length at bound
    simp [Bao.RangeRequest.valid, decide_eq_true_eq]
    omega
  have partition : Bao.sliceChunks original.length window = ⟨0, 1⟩ := by
    simp [Bao.sliceChunks, chunks_one small]
  have hdr := Bao.readHeader_putLE64 original validWire
  have emptyHdr : Bao.readHeader (Bao.putLE64 original.length) = some (original.length, []) := by
    simpa using Bao.readHeader_putLE64 [] validWire
  cases profile with
  | combined =>
    have decodeWire : Bao.decode .combined (Bao.putLE64 original.length ++ original) =
        some (original.length, [original]) := by
      apply Bao.decode_spec.mpr
      simp [Bao.Encoding.valid, Bao.Encoding.bodyFits, chunks_one small, hdr, Bao.Encoding.layout,
        full, leafPlan, Bao.Plan.preorder, Bao.Tape, Bao.Slot.width]
    refine ⟨Bao.putLE64 original.length ++ original, response, ?_, ?_, claim, eof, data⟩
    · simp [encode?, Profile.encoding, Bao.encode, validWire, Bao.Encoding.valid, Bao.Encoding.layout,
        full, leafPlan, Bao.Plan.preorder, Bao.writeSlots, Bao.Slot.width]
    · simp [decode?, decodeCombined?, checkBaoInline?, hdr, Nat.not_lt.mpr withinCap, InlineEncoding.encoding]
      split
      · rename_i failed; exact nomatch decodeWire.symm.trans failed
      · rename_i size fields parsed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (decodeWire.symm.trans parsed))
        simp [InlineEncoding.plan, full, check, project]
  | slice =>
    have decodeWire : Bao.decode (.slice window) (Bao.putLE64 original.length ++ original) =
        some (original.length, [original]) := by
      apply Bao.decode_spec.mpr
      simp [Bao.Encoding.valid, Bao.Encoding.bodyFits, partition, Bao.chunkBytes, Nat.min_eq_left small,
        windowValid, hdr, Bao.Encoding.layout, slice, leafPlan, Bao.Plan.preorder, Bao.Tape, Bao.Slot.width]
    refine ⟨Bao.putLE64 original.length ++ original, response, ?_, ?_, claim, eof, data⟩
    · simp [encode?, Profile.encoding, Bao.encode, validWire, Bao.Encoding.valid, windowEq, windowValid,
        Bao.Encoding.layout, slice, leafPlan, Bao.Plan.preorder, Bao.writeSlots, Bao.Slot.width]
    · simp [decode?, decodeSlice?, checkBaoInline?, hdr, Nat.not_lt.mpr withinCap, InlineEncoding.encoding]
      split
      · rename_i failed; exact nomatch decodeWire.symm.trans failed
      · rename_i size fields parsed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (decodeWire.symm.trans parsed))
        simp [InlineEncoding.plan, windowEq, slice, check, project]
  | outboard =>
    have decodeWire : Bao.decode .outboard (Bao.putLE64 original.length) =
        some (original.length, []) := by
      apply Bao.decode_spec.mpr
      simp [Bao.Encoding.valid, Bao.Encoding.bodyFits, chunks_one small, emptyHdr, Bao.Encoding.layout,
        full, leafPlan, Bao.Plan.pairs, Bao.Tape]
    have take : Bao.takeExact original.length original = some (original, []) :=
      Bao.takeExact_spec.mpr ⟨rfl, (List.append_nil _).symm⟩
    refine ⟨Bao.putLE64 original.length, response, ?_, ?_, claim, eof, data⟩
    · simp [encode?, Profile.encoding, Bao.encode, validWire, Bao.Encoding.valid, Bao.Encoding.layout,
        full, leafPlan, Bao.Plan.pairs, Bao.writeSlots]
    · simp [decode?, decodeOutboard?, checkBaoOutboard?, emptyHdr, Nat.not_lt.mpr withinCap]
      split
      · rename_i failed; exact nomatch decodeWire.symm.trans failed
      · rename_i size fields parsed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (decodeWire.symm.trans parsed))
        let body := leafBody small valid digestEq hit
        have pairs : body.tape.pairs = [] := rfl
        have originalData : (body.tape.spans.map SpanFact.bytes).flatten = original := by
          simp [body, leafBody, Tape.spans]
        have offsets : ∀ fact ∈ body.tape.spans, fact.offset + fact.bytes.length ≤ original.length ∧
            (original.drop fact.offset).take fact.bytes.length = fact.bytes := by
          simp [body, leafBody, Tape.spans]
        have sourceEq : (Bao.fullPlan original.length 1).preorder.mapM
            (Bao.outboardSource (Bao.positioned ((Bao.fullPlan original.length 1).pairs false) []) original) =
            some [original] := by
          simp [full, leafPlan, Bao.Plan.pairs, Bao.Plan.preorder, Bao.outboardSource, span, Bao.Span.byteStart, take]
        simp only [sourceEq, Option.bind_some]
        simp [full, check, SpanFact.matches]
        dsimp only [body] at pairs originalData offsets
        simp only [dite_eq_left pairs, dite_eq_left originalData, dite_eq_left offsets, Option.bind_some]
        exact project

end Silmaril.Proofs.Formats.Blake3Cas.RangeFacts.SingleChunk
