module

public import Silmaril.Formats.Arrow.StructInt32.Stream.Defs
import Silmaril.Formats.Arrow.Body.Thms
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Arrow.StructInt32.Stream

open Silmaril.Formats.Arrow hiding Row readRows
open Silmaril.Formats.Arrow.StructInt32.Stream

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

theorem readRow_wire {field : StructInt32.Field} {bitmap : KBytes} {left right : Array (Option Int32)}
    {index : Nat} {row : Row} (read : readRow field bitmap left right index = .ok row) :
    RowWire field bitmap left right index row := by
  cases valid : Body.validAt bitmap index with
  | none => simp [readRow, valid] at read
  | some bit =>
    cases bit with
    | false => exact ⟨false, valid, by simpa [readRow, valid] using read.symm⟩
    | true =>
      cases first : left[index]? with
      | none => simp [readRow, valid, first] at read
      | some lhs =>
        cases second : right[index]? with
        | none => simp [readRow, valid, first, second] at read
        | some rhs =>
          cases admitted : missingRequired field (lhs, rhs) with
          | some position => simp [readRow, valid, first, second, admitted] at read
          | none =>
            have same : row = some (lhs, rhs) := by simpa [readRow, valid, first, second, admitted] using read.symm
            exact ⟨true, valid, lhs, rhs, first, second, admitted, same⟩

theorem readRows_wire {field : StructInt32.Field} {layout : Layout} {body : KBytes} {rows : List Row}
    (read : readRows field layout body = .ok rows) : RowsWire field layout body rows := by
  unfold readRows at read
  split at read
  · contradiction
  · rename_i fit
    dsimp only at read
    split at read
    · contradiction
    · rename_i bitmap
      obtain ⟨left, first, read⟩ := bind_ok read
      obtain ⟨right, second, read⟩ := bind_ok read
      obtain ⟨values, decoded, read⟩ := bind_ok read
      split at read
      · contradiction
      · rename_i count
        cases Except.ok.inj read
        have slots := (List.mapM_eq_ok_iff_forall₂.mp decoded).imp
          (fun _ _ read => readRow_wire read)
        exact ⟨Decidable.of_not_not fit, Decidable.of_not_not bitmap, by simpa using slots.length_eq.symm,
          Decidable.of_not_not count, left, right, (Body.readColumn_iff _ _ _).mp (mapError_ok first),
          (Body.readColumn_iff _ _ _).mp (mapError_ok second), slots⟩

private theorem layout_exact {metadata : RecordBatch} {layout : Layout}
    (checked : layoutOf metadata = .ok layout) :
    metadata.nodes = layout.nodes ∧ metadata.buffers = layout.buffers ∧
      layout.parent.length = metadata.rowCount ∧ layout.left.length = metadata.rowCount ∧
      layout.right.length = metadata.rowCount := by
  unfold layoutOf at checked
  split at checked
  · split at checked
    · rename_i same
      cases Except.ok.inj checked
      exact ⟨by assumption, by assumption, same.1, same.2.1.trans same.1, same.2.2.trans same.1⟩
    · contradiction
  · contradiction

theorem readRecord_wire {limits : ObservationLimits} {field : StructInt32.Field} {input : KBytes}
    {rowsBefore offset size : Nat} {batch : Batch}
    (read : readRecord limits field input rowsBefore offset size = .ok batch) :
    RecordWire limits field input rowsBefore offset size batch := by
  unfold readRecord at read
  obtain ⟨message, parsed, read⟩ := bind_ok read
  split at read
  · rename_i metadata header
    obtain ⟨layout, layoutRead, read⟩ := bind_ok read
    obtain ⟨_, budget, read⟩ := bind_ok read
    obtain ⟨body, bodyRead, read⟩ := bind_ok read
    obtain ⟨rows, rowsRead, read⟩ := bind_ok read
    cases Except.ok.inj read
    obtain ⟨nodes, buffers, parent, left, right⟩ := layout_exact layoutRead
    have matched : message = ⟨.recordBatch metadata, message.bodyLength⟩ := by cases message; simp_all
    exact ⟨metadata, layout, body, matched ▸ mapError_ok parsed, layoutRead, nodes, buffers, parent,
      left, right, mapError_ok budget, mapError_ok bodyRead, readRows_wire rowsRead, rfl, rfl⟩
  · contradiction

private theorem readBatches_wire {limits : ObservationLimits} {field : StructInt32.Field} {input : KBytes}
    {fuel index rowsBefore offset : Nat} {batches : List Batch}
    (read : readBatches limits field input fuel index rowsBefore offset = .ok batches) :
    BatchesWire limits field input fuel rowsBefore offset batches := by
  induction fuel generalizing index rowsBefore offset batches with
  | zero =>
    rw [readBatches] at read
    obtain ⟨env, envelope, read⟩ := bind_ok read
    cases env with
    | metadata size => contradiction
    | eos =>
      change (if offset + 8 = input.len then Except.ok [] else
        Except.error (Error.batch index .trailingBytes)) = .ok batches at read
      split at read
      · obtain rfl := Except.ok.inj read
        exact .eos (mapError_ok envelope) (by assumption)
      · contradiction
  | succ fuel ih =>
    rw [readBatches] at read
    obtain ⟨env, envelope, read⟩ := bind_ok read
    cases env with
    | eos =>
      change (if offset + 8 = input.len then Except.ok [] else
        Except.error (Error.batch index .trailingBytes)) = .ok batches at read
      split at read
      · obtain rfl := Except.ok.inj read
        exact .eos (mapError_ok envelope) (by assumption)
      · contradiction
    | metadata size =>
      obtain ⟨batch, record, read⟩ := bind_ok read
      obtain ⟨rest, later, read⟩ := bind_ok read
      obtain rfl := Except.ok.inj read
      exact .next (mapError_ok envelope) (readRecord_wire (mapError_ok record)) (ih later)

theorem read_wire {limits : ObservationLimits} {input : KBytes} {observed : Observed}
    (checked : StructInt32.Stream.read limits input = .ok observed) :
    input.wf = true ∧ ∃ size,
      readEnvelope limits.ipc input 0 = .ok (.metadata size) ∧
      StructInt32.readSchema limits.ipc (input.slice 8 size) = .ok observed.field ∧
      BatchesWire limits observed.field input limits.ipc.batches 0 (8 + size) observed.batches := by
  unfold StructInt32.Stream.read at checked
  split at checked
  · contradiction
  · rename_i wf
    obtain ⟨⟨field, first⟩, schemaFrame, checked⟩ := bind_ok checked
    obtain ⟨batches, records, checked⟩ := bind_ok checked
    cases Except.ok.inj checked
    unfold readSchemaFrame at schemaFrame
    obtain ⟨env, envelope, schemaFrame⟩ := bind_ok schemaFrame
    cases env with
    | eos => contradiction
    | metadata size =>
      obtain ⟨header, schema, schemaFrame⟩ := bind_ok schemaFrame
      cases Except.ok.inj schemaFrame
      exact ⟨by simpa using wf, size, mapError_ok envelope, mapError_ok schema, readBatches_wire records⟩

end Silmaril.Proofs.Formats.Arrow.StructInt32.Stream
