module

public import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Defs
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Chunk.Page

@[expose] public section

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Chunk

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema (Compiled ChunkBinding)
open Silmaril.Formats.Parquet.RecursiveSchema.Chunk

private def WalkResult (limits : Limits) (carrier : Carrier) (cursor : Cursor)
    (reversed pages : List ObservedPage) : Prop :=
  ∃ stop tail, pages = reversed.reverse ++ tail ∧ stop.byte = carrier.span.stop ∧
    stop.row = carrier.expected ∧ ChainWire limits carrier cursor stop tail

private theorem walk_final {limits : Limits} {carrier : Carrier} {budget : Nat} {cursor : Cursor}
    {reversed pages : List ObservedPage} (ending : cursor.byte = carrier.span.stop)
    (read : walk limits carrier budget cursor reversed = .ok pages) :
    WalkResult limits carrier cursor reversed pages := by
  by_cases count : cursor.row = carrier.expected
  · have result : reversed.reverse = pages := by
      cases budget <;> simpa [walk, ending, count] using read
    exact ⟨cursor, [], by simp [result], ending, count, .nil cursor⟩
  · cases budget <;> simp [walk, ending, count] at read

private theorem walk_wire {limits : Limits} {carrier : Carrier} {budget : Nat} {cursor : Cursor}
    {reversed pages : List ObservedPage}
    (read : walk limits carrier budget cursor reversed = .ok pages) :
    WalkResult limits carrier cursor reversed pages := by
  induction budget generalizing cursor reversed pages with
  | zero =>
    by_cases ending : cursor.byte = carrier.span.stop
    · exact walk_final ending read
    · simp [walk, ending] at read
  | succ fuel ih =>
    by_cases ending : cursor.byte = carrier.span.stop
    · exact walk_final ending read
    · simp only [walk, ending, ite_false] at read
      cases parsed : Page.readPage limits.framing carrier.bytes carrier.span cursor.byte with
      | error reason => simp [parsed, Except.mapError, bind, Except.bind] at read
      | ok frame =>
        cases decoded : decodePage limits carrier.leaf carrier.bytes frame cursor.row
            (carrier.expected - cursor.row) with
        | error reason => simp [parsed, decoded, Except.mapError, bind, Except.bind] at read
        | ok slots =>
          simp only [parsed, decoded, Except.mapError, bind, Except.bind] at read
          let page : ObservedPage := ⟨frame, cursor.row, slots⟩
          obtain ⟨stop, tail, pages, byte, row, chain⟩ := ih (reversed := page :: reversed) read
          refine ⟨stop, page :: tail, ?_, byte, row, .more parsed rfl (decodePage_wire decoded) chain⟩
          simpa [List.reverse_cons, List.append_assoc] using pages

theorem chain_frames {limits : Limits} {carrier : Carrier} {start stop : Cursor}
    {pages : List ObservedPage} (bound : ChainWire limits carrier start stop pages) :
    Page.Chain carrier.span start.byte stop.byte (pages.map ObservedPage.frame) := by
  induction bound with
  | nil cursor => exact .nil cursor.byte
  | more parsed _ _ _ ih => exact .cons (Page.readPage_within parsed).1 ih

theorem chain_rows {limits : Limits} {carrier : Carrier} {start stop : Cursor}
    {pages : List ObservedPage} (bound : ChainWire limits carrier start stop pages) :
    start.row + (pages.flatMap ObservedPage.slots).length = stop.row := by
  induction bound with
  | nil => simp
  | more _ _ _ _ ih =>
    simpa only [List.flatMap_cons, List.length_append, Cursor.advance, ← Nat.add_assoc] using ih

theorem read_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    {limits : Limits} {binding : ChunkBinding schema group column} {output : Observation}
    (accepted : Formats.Parquet.RecursiveSchema.Chunk.read limits binding = .ok output) :
    Wire limits binding output := by
  unfold Formats.Parquet.RecursiveSchema.Chunk.read at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  · rename_i within
    split at accepted
    · contradiction
    · rename_i bytes
      split at accepted
      · contradiction
      · rename_i rows
        split at accepted
        · contradiction
        · rename_i uncompressed
          cases walked : walk limits (carrierOf binding) limits.framing.maxPages
              (initial (carrierOf binding)) [] with
          | error reason => simp [walked, Except.map] at accepted
          | ok pages =>
            simp only [walked, Except.map, Except.ok.injEq] at accepted
            subst output
            obtain ⟨stop, tail, ordered, byte, row, chain⟩ := walk_wire walked
            simp only [List.reverse_nil, List.nil_append] at ordered
            subst tail
            have total := chain_rows chain
            have frames := chain_frames chain
            exact ⟨Classical.not_not.mp within, Nat.le_of_not_gt bytes, Nat.le_of_not_gt rows, Classical.not_not.mp uncompressed,
              ⟨stop, byte, row, chain⟩, byte ▸ frames, by simpa [initial, Observation.rows, carrierOf] using total.trans row⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Chunk
