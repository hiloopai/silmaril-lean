module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi

open Silmaril.Formats (Bytes)
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi

private theorem packPages_wire {limits : Chunk.Limits} {input : Input}
    {start : Chunk.Cursor} {pages : List (List Rows.Atom)} {reversed : List Writer.Output}
    {packed : Packed} (written : packPages limits input pages start reversed = .ok packed) :
    ∃ pieces, packed.pieces = reversed.reverse ++ pieces ∧
      PiecesWire limits input start packed.stop pages pieces := by
  induction pages generalizing start reversed with
  | nil =>
    cases Except.ok.inj written
    exact ⟨[], by simp, .nil _⟩
  | cons atoms rest ih =>
    simp only [packPages] at written
    cases page : Writer.serialize (remainingLimits limits start) (input.page start.state atoms) with
    | error cause => simp [page, Except.mapError, bind, Except.bind] at written
    | ok piece =>
      simp only [page, Except.mapError, bind, Except.bind] at written
      obtain ⟨pieces, ordered, tail⟩ := ih written
      exact ⟨piece :: pieces, by simpa [List.reverse_cons, List.append_assoc] using ordered,
        .cons page (Writer.serialize_construction page) tail⟩

private theorem assemble_from (pieces : List Writer.Output) (acc : Bytes) :
    pieces.foldl (fun bytes page => bytes.append page.wire) acc = acc.append (assemble pieces) := by
  induction pieces generalizing acc with
  | nil => simp [assemble]
  | cons piece pieces ih =>
    simp only [List.foldl_cons, ih]
    conv_rhs => rw [assemble, List.foldl_cons, ih, Bytes.empty_append]
    rw [Bytes.append_assoc]

private theorem assemble_cons (piece : Writer.Output) (pieces : List Writer.Output) :
    assemble (piece :: pieces) = piece.wire.append (assemble pieces) := by
  unfold assemble
  rw [List.foldl_cons, Bytes.empty_append]
  exact assemble_from pieces piece.wire

public theorem assemble_ordered (pieces : List Writer.Output) :
    (assemble pieces).toList = (pieces.map (fun piece => piece.wire.toList)).flatten := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih => simp [assemble_cons, ih]

private theorem byte_extents {limits : Chunk.Limits} {input : Input} {start stop : Chunk.Cursor}
    {pages : List (List Rows.Atom)} {pieces : List Writer.Output}
    (wire : PiecesWire limits input start stop pages pieces) (bounded : start.byte ≤ limits.maxChunkBytes) :
    stop.byte = start.byte + (assemble pieces).length ∧ stop.byte ≤ limits.maxChunkBytes := by
  induction wire with
  | nil cursor => exact ⟨by simp [assemble], bounded⟩
  | @cons start stop atoms rest piece pieces _ built _ ih =>
    have cap := built.frameCap
    simp only [remainingLimits, Writer.Output.wire, Formats.Parquet.PlainV1Writer.Encoded.wire,
      Bytes.length_append] at cap
    change frameSize piece ≤ limits.maxChunkBytes - start.byte at cap
    have step : (advance start piece).byte ≤ limits.maxChunkBytes := by
      change start.byte + frameSize piece ≤ limits.maxChunkBytes
      omega
    obtain ⟨extent, finalCap⟩ := ih step
    exact ⟨by simpa [assemble_cons, advance, frameSize, Writer.Output.wire,
      Formats.Parquet.PlainV1Writer.Encoded.wire, Nat.add_assoc] using extent, finalCap⟩

public theorem construction {limits : Chunk.Limits} {input : Input} {packed : Packed}
    (written : serialize limits input = .ok packed) : Construction limits input packed := by
  unfold serialize at written
  split at written
  · contradiction
  · rename_i partition
    split at written
    · contradiction
    · rename_i pages
      split at written
      · contradiction
      · rename_i slots
        split at written
        · contradiction
        · rename_i rows
          obtain ⟨pieces, ordered, wire⟩ := packPages_wire written
          simp only [List.reverse_nil, List.nil_append] at ordered
          subst pieces
          obtain ⟨extent, bounded⟩ := byte_extents wire (Nat.zero_le _)
          simp only [Writer.Multi.initial, Nat.zero_add] at extent
          exact ⟨by simpa using partition, Nat.le_of_not_gt pages, Nat.le_of_not_gt slots,
            Nat.le_of_not_gt rows, extent ▸ bounded, extent, wire⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi
