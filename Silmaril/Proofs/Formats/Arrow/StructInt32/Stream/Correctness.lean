module

public import Silmaril.Formats.Arrow.StructInt32.Stream.Defs
import Silmaril.Formats.Arrow.Body.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Arrow.StructInt32.Stream

open Silmaril.Formats.Arrow hiding Row readRows
open Silmaril.Formats.Arrow.StructInt32.Stream
open Silmaril.Formats.Arrow.StructInt32 (RightWidth)
open Silmaril.Formats.Parquet

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

theorem readRowFor_wire {α : Type} {field : StructInt32.Field} {bitmap : KBytes}
    {left : Array (Option Int32)} {right : Array (Option α)}
    {index : Nat} {row : RowFor α} (read : readRowFor field bitmap left right index = .ok row) :
    RowWireFor field bitmap left right index row := by
  cases valid : Body.validAt bitmap index with
  | none => simp [readRowFor, valid] at read
  | some bit =>
    cases bit with
    | false => exact ⟨false, valid, by simpa [readRowFor, valid] using read.symm⟩
    | true =>
      cases first : left[index]? with
      | none => simp [readRowFor, valid, first] at read
      | some lhs =>
        cases second : right[index]? with
        | none => simp [readRowFor, valid, first, second] at read
        | some rhs =>
          cases admitted : missingRequiredFor field (lhs, rhs) with
          | some position => simp [readRowFor, valid, first, second, admitted] at read
          | none =>
            have same : row = some (lhs, rhs) := by simpa [readRowFor, valid, first, second, admitted] using read.symm
            exact ⟨true, valid, lhs, rhs, first, second, admitted, same⟩

private theorem wideSlot_wire {bitmap : KBytes} {entry : Int64 × Nat} {slot : Option Int64}
    (read : wideSlot bitmap entry = .ok slot) :
    ∃ valid, Body.validAt bitmap entry.2 = some valid ∧ slot = (if valid then some entry.1 else none) := by
  cases valid : Body.validAt bitmap entry.2 with
  | none => simp [wideSlot, valid] at read
  | some bit =>
    exact ⟨bit, rfl, by simpa [wideSlot, valid, pure, Except.pure] using read.symm⟩

theorem readWideColumn_wire {node : FieldNode} {bitmap values : KBytes} {slots : List (Option Int64)}
    (read : readWideColumn node bitmap values = .ok slots) : WideColumnWire node bitmap values slots := by
  unfold readWideColumn at read
  split at read
  · contradiction
  · rename_i bitmapFits
    dsimp only at read
    split at read
    · contradiction
    · rename_i extent
      obtain ⟨decoded, decodedOk, read⟩ := bind_ok read
      obtain ⟨placed, placedOk, read⟩ := bind_ok read
      split at read
      · contradiction
      · rename_i count
        cases Except.ok.inj read
        have raw := mapError_ok decodedOk
        change Plain.decodeFixedWidth 8 node.length _ _ = .ok decoded at raw
        obtain ⟨_, words, fromBytes, length, sized, reconstruct⟩ := Plain.decodeFixedWidth_ok_iff.mp raw
        have positions : words.zipIdx.mapM
            (fun (word, index) => wideSlot bitmap ((UInt64.ofNat (KBytes.leVal word)).toInt64, index)) =
              .ok slots := by
          rw [reconstruct, List.zipIdx_map, List.mapM_map] at placedOk
          exact placedOk
        exact ⟨Decidable.of_not_not bitmapFits, Nat.le_of_not_gt extent, Decidable.of_not_not count,
          words, fromBytes, length, sized, (List.mapM_eq_ok_iff_forall₂.mp positions).imp
            (fun _ _ slotRead => wideSlot_wire slotRead)⟩

private theorem readRightColumn_wire {width : RightWidth} {layout : Layout} {body : KBytes}
    {slots : RightPhysical width} (read : readRightColumn width layout body = .ok slots) :
    RightColumnWire width layout body slots := by
  cases width with
  | int32 => exact (Body.readColumn_iff _ _ _).mp read
  | int64 => exact readWideColumn_wire read

theorem readRowsFor_wire {width : RightWidth} {field : StructInt32.Field}
    {layout : Layout} {body : KBytes} {rows : List (RowFor width.Value)}
    (read : readRowsFor width field layout body = .ok rows) : RowsWireFor width field layout body rows := by
  unfold readRowsFor at read
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
          (fun _ _ read => readRowFor_wire read)
        exact ⟨Decidable.of_not_not fit, Decidable.of_not_not bitmap, by simpa using slots.length_eq.symm,
          Decidable.of_not_not count, left, right, (Body.readColumn_iff _ _ _).mp (mapError_ok first),
          readRightColumn_wire (mapError_ok second), slots⟩

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

theorem readRecordFor_wire {width : RightWidth} {limits : ObservationLimits}
    {field : StructInt32.Field} {input : KBytes}
    {rowsBefore offset size : Nat} {batch : Batch width.Value}
    (read : readRecordFor width limits field input rowsBefore offset size = .ok batch) :
    RecordWireFor width limits field input rowsBefore offset size batch := by
  unfold readRecordFor at read
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
      left, right, mapError_ok budget, mapError_ok bodyRead, readRowsFor_wire rowsRead, rfl, rfl⟩
  · contradiction

private theorem readBatchesFor_wire {width : RightWidth} {limits : ObservationLimits}
    {field : StructInt32.Field} {input : KBytes}
    {fuel index rowsBefore offset : Nat} {batches : List (Batch width.Value)}
    (read : readBatchesFor width limits field input fuel index rowsBefore offset = .ok batches) :
    BatchesWireFor width limits field input fuel rowsBefore offset batches := by
  induction fuel generalizing index rowsBefore offset batches with
  | zero =>
    rw [readBatchesFor] at read
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
    rw [readBatchesFor] at read
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
      exact .next (mapError_ok envelope) (readRecordFor_wire (mapError_ok record)) (ih later)

theorem readFor_wire {width : RightWidth} {limits : ObservationLimits} {input : KBytes}
    {observed : Observed width.Value}
    (checked : readFor width limits input = .ok observed) :
    input.wf = true ∧ ∃ size,
      readEnvelope limits.ipc input 0 = .ok (.metadata size) ∧
      StructInt32.readSchemaFor width limits.ipc (input.slice 8 size) = .ok observed.field ∧
      BatchesWireFor width limits observed.field input limits.ipc.batches 0 (8 + size) observed.batches := by
  unfold readFor at checked
  split at checked
  · contradiction
  · rename_i wf
    obtain ⟨⟨field, first⟩, schemaFrame, checked⟩ := bind_ok checked
    obtain ⟨batches, records, checked⟩ := bind_ok checked
    cases Except.ok.inj checked
    unfold readSchemaFrameFor at schemaFrame
    obtain ⟨env, envelope, schemaFrame⟩ := bind_ok schemaFrame
    cases env with
    | eos => contradiction
    | metadata size =>
      obtain ⟨header, schema, schemaFrame⟩ := bind_ok schemaFrame
      cases Except.ok.inj schemaFrame
      exact ⟨by simpa using wf, size, mapError_ok envelope, mapError_ok schema, readBatchesFor_wire records⟩

end Silmaril.Proofs.Formats.Arrow.StructInt32.Stream
