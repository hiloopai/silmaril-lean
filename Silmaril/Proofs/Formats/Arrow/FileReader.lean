module

public import Silmaril.Formats.Arrow.FileReader.Defs
import Silmaril.Formats.Arrow.Framing.Thms
import Silmaril.Prelude.Bytes.Thms
import Init.Data.List.Monadic
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.FileReader

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.FileReader

theorem readFooterSpan_verified {limits : Limits} {input : KBytes} {span : FooterSpan input}
    (read : readFooterSpan limits input = .ok span) :
    input.read 0 6 = magic ∧ input.read 6 2 = 0 ∧ input.read (input.len - 6) 6 = magic ∧
      input.read (input.len - 10) 4 = span.length ∧ span.length < 2^31 ∧
      span.length ≤ limits.metadataBytes ∧ 8 ≤ span.start := by
  simp only [readFooterSpan] at read
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  cases read
  simp_all
  omega

theorem footer_exact {input : KBytes} (span : FooterSpan input) :
    (input.slice span.start span.length).toList =
      (input.toList.drop span.start).take span.length :=
  KBytes.toList_slice _ _ _ span.source (by have := span.extent; omega)

theorem block_range {footerStart cursor : Nat} {blocks : List FileBlock}
    (fits : BlocksFit footerStart cursor blocks) {block : FileBlock} (member : block ∈ blocks) :
    cursor ≤ block.offset ∧ block.offset % 8 = 0 ∧ 8 ≤ block.metadataLength ∧
      block.metadataLength % 8 = 0 ∧ block.bodyLength % 8 = 0 ∧
      block.endOffset ≤ footerStart := by
  induction blocks generalizing cursor with
  | nil => simp at member
  | cons head tail ih =>
    obtain ⟨atCursor, aligned, hasEnvelope, metaAlign, bodyAlign, bounded, later⟩ := fits
    rcases List.mem_cons.mp member with same | rest
    · subst block
      exact ⟨Nat.le_of_eq atCursor.symm, aligned, hasEnvelope, metaAlign, bodyAlign, bounded⟩
    · obtain ⟨next, offAlign, hasPrefix, mdAlign, dataAlign, ends⟩ := ih later rest
      have advance : cursor ≤ head.endOffset := by unfold FileBlock.endOffset; omega
      exact ⟨Nat.le_trans advance next, offAlign, hasPrefix, mdAlign, dataAlign, ends⟩

theorem block_order {footerStart cursor : Nat} {blocks : List FileBlock}
    (fits : BlocksFit footerStart cursor blocks) :
    List.Pairwise (fun earlier later : FileBlock => earlier.endOffset ≤ later.offset) blocks := by
  induction blocks generalizing cursor with
  | nil => exact .nil
  | cons head tail ih =>
    have rest := fits.2.2.2.2.2.2
    exact .cons (fun _ member => (block_range rest member).1) (ih rest)

theorem readBlock_exact {input : KBytes} (index : Index input) (limits : Limits)
    {block : FileBlock} (member : block ∈ index.footer.blocks)
    {frame : BatchFrame index.footer.fields}
    (read : index.readBlock limits block member = .ok frame) :
    readEnvelope limits input block.offset = .ok (.metadata (block.metadataLength - 8)) ∧
      readMessage limits (input.slice (block.offset + 8) (block.metadataLength - 8)) =
        .ok ⟨.recordBatch frame.metadata, block.bodyLength⟩ ∧
      frame.body.len = block.bodyLength ∧ frame.body.toList =
        (input.toList.drop (block.offset + block.metadataLength)).take block.bodyLength := by
  cases prefixRead : readEnvelope limits input block.offset with
  | error error => simp [Index.readBlock, prefixRead, bind, Except.bind] at read
  | ok envelope =>
    cases envelope with
    | eos => simp [Index.readBlock, prefixRead, bind, Except.bind] at read
    | metadata size =>
      by_cases sizeMatches : 8 + size = block.metadataLength
      · cases decoded : readMessage limits (input.slice (block.offset + 8) size) with
        | error error => simp [Index.readBlock, prefixRead, sizeMatches, decoded, bind, Except.bind] at read
        | ok message =>
          obtain ⟨header, length⟩ := message
          cases header with
          | schema fields => simp [Index.readBlock, prefixRead, sizeMatches, decoded, bind, Except.bind] at read
          | recordBatch metadata =>
            by_cases lengthMatches : length = block.bodyLength
            · cases bodyRead : readBody limits input (block.offset + block.metadataLength) block.bodyLength with
              | error error =>
                simp [Index.readBlock, prefixRead, sizeMatches, decoded, lengthMatches, bodyRead,
                  bind, Except.bind] at read
              | ok body =>
                simp [Index.readBlock, prefixRead, sizeMatches, decoded, lengthMatches, bodyRead,
                  bind, Except.bind] at read
                unfold validateBatch at read
                split at read <;> try contradiction
                cases read
                have width : block.metadataLength - 8 = size := by omega
                exact ⟨by rw [width], by rw [width, decoded, lengthMatches],
                  body_exact index.span.source bodyRead⟩
            · simp [Index.readBlock, prefixRead, sizeMatches, decoded, lengthMatches, bind, Except.bind] at read
      · simp [Index.readBlock, prefixRead, sizeMatches, bind, Except.bind] at read

private theorem mapM_index {α β : Type} {f : α → Except Error β} {xs : List α} {ys : List β}
    (read : xs.mapM f = .ok ys) :
    ys.length = xs.length ∧ ∀ n : Nat, xs[n]?.mapM f = .ok ys[n]? := by
  induction xs generalizing ys with
  | nil =>
    have empty : ys = [] := by simpa [pure, Except.pure] using read.symm
    subst ys
    exact ⟨rfl, fun n => by simp [Option.mapM, pure, Except.pure]⟩
  | cons first rest ih =>
    cases firstRead : f first with
    | error error => simp [List.mapM_cons, firstRead, bind, Except.bind] at read
    | ok value =>
      cases restRead : rest.mapM f with
      | error error => simp [List.mapM_cons, firstRead, restRead, bind, Except.bind] at read
      | ok tail =>
        simp [List.mapM_cons, firstRead, restRead, bind, Except.bind, pure, Except.pure] at read
        subst ys
        obtain ⟨length, indexed⟩ := ih restRead
        refine ⟨by simp [length], fun n => ?_⟩
        cases n with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.mapM, firstRead]
          rfl
        | succ n => exact indexed n

theorem readRows_indexed {limits : ObservationLimits} {input : KBytes} {observed : ObservedFile}
    (read : FileReader.readRows limits input = .ok observed) :
    ∃ index : Index input, readIndex limits.ipc input = .ok index ∧
      observed.fields = index.footer.fields ∧
      observed.batches.length = index.footer.blocks.length ∧
      ∀ n, index.readRowsAt limits n = .ok observed.batches[n]? := by
  cases checked : readIndex limits.ipc input with
  | error error => simp [FileReader.readRows, checked, bind, Except.bind] at read
  | ok index =>
    cases framesRead : index.readBatches limits.ipc with
    | error error => simp [FileReader.readRows, checked, framesRead, bind, Except.bind] at read
    | ok frames =>
      cases budget : Body.checkBudget limits index.footer.fields.length
          (frames.map (·.metadata.rowCount)).sum with
      | error error => simp [FileReader.readRows, checked, framesRead, budget, bind, Except.bind] at read
      | ok success =>
        cases rowsRead : frames.mapM (decodeBatch limits) with
        | error error => simp [FileReader.readRows, checked, framesRead, budget, rowsRead, bind, Except.bind] at read
        | ok rows =>
          simp [FileReader.readRows, checked, framesRead, budget, rowsRead, bind, Except.bind, pure, Except.pure] at read
          subst observed
          obtain ⟨frameCount, frameAt⟩ := mapM_index framesRead
          obtain ⟨rowCount, rowsAt⟩ := mapM_index rowsRead
          refine ⟨index, rfl, rfl, rowCount.trans (frameCount.trans List.length_attach), fun n => ?_⟩
          have frameRead : index.readBatchAt limits.ipc n = .ok frames[n]? := frameAt n
          simpa only [Index.readRowsAt, frameRead, bind, Except.bind] using rowsAt n

end Silmaril.Proofs.Formats.Arrow.FileReader
