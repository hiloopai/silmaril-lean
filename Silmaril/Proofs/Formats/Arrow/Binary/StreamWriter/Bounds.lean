module

public import Silmaril.Formats.Arrow.Binary.StreamWriter.Defs
import Silmaril.Formats.Arrow.StreamWriter.Thms
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Thms
import Init.Data.List.Scan.Lemmas
import Batteries.Data.List.Lemmas
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Arrow.Binary.StreamWriter

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open Binary.StreamWriter

private theorem checkRecord_exact {width : Binary.Offsets.Width} {limits : Limits}
    {nullable : Bool} {values : Binary.Column} {node : FieldNode}
    (checked : checkRecordFor width limits nullable values = .ok node) :
    node = ⟨values.length, values.countP Option.isNone⟩ ∧ RecordBounds width limits values ∧
      ∀ piece ∈ values.filterMap id, piece.wf = true := by
  by_cases rows : values.length > limits.rows
  · simp [checkRecordFor, rows] at checked
  by_cases nulls : (!nullable && values.countP Option.isNone != 0) = true
  · simp [checkRecordFor, rows, nulls] at checked
  by_cases offsets : dataSize values ≥ width.signedLimit
  · simp [checkRecordFor, rows, nulls, offsets] at checked
  by_cases body : bodySizeFor width values.length (dataSize values) > limits.bodyBytes
  · simp [checkRecordFor, rows, nulls, offsets, body] at checked
  by_cases size : values.length ≥ 2^63 ∨ bodySizeFor width values.length (dataSize values) ≥ 2^63
  · simp [checkRecordFor, rows, nulls, offsets, body, size] at checked
  by_cases wf : (values.all (fun value => (value.map KBytes.wf).getD true)) = true
  · have exactNode : node = ⟨values.length, values.countP Option.isNone⟩ := by
      simpa [checkRecordFor, rows, nulls, offsets, body, size, wf, Pure.pure, Except.pure] using checked.symm
    refine ⟨exactNode, ⟨Nat.le_of_not_gt rows, Nat.lt_of_not_ge offsets, Nat.le_of_not_gt body⟩, ?_⟩
    intro piece mem
    obtain ⟨value, occurs, rfl⟩ := List.mem_filterMap.mp mem
    exact (List.all_eq_true.mp wf) _ occurs
  · simp [checkRecordFor, rows, nulls, offsets, body, size, wf] at checked

private theorem dataSize_prefix (values : Binary.Column) (start : Nat) :
    values.foldl (fun offset value => offset + valueSize value) start = start + dataSize values := by
  induction values generalizing start with
  | nil => simp [dataSize]
  | cons value rest ih =>
    simp only [dataSize, List.foldl_cons, Nat.zero_add]
    rw [ih (start + valueSize value), ih (valueSize value), Nat.add_assoc]

private theorem dataSize_sum (values : Binary.Column) :
    dataSize values = ((values.filterMap id).map KBytes.len).sum := by
  induction values with
  | nil => rfl
  | cons slot rest ih =>
    change rest.foldl (fun offset value => offset + valueSize value) (0 + valueSize slot) = _
    rw [Nat.zero_add, dataSize_prefix, ih]
    cases slot <;> simp [valueSize, KBytes.empty, KBytes.len]

private theorem encoded_exact {width : Binary.Offsets.Width} {values : Binary.Column}
    (signed : dataSize values < width.signedLimit)
    (wf : ∀ piece ∈ values.filterMap id, piece.wf = true) :
    ColumnWire width values (encodeColumn width values) ∧
      ∀ part ∈ columnPartsFor width values, part.wf = true := by
  have joined := BinaryView.Column.Writer.join_spec (values.filterMap id) wf
  have offsetsLength : (offsetWords values).length = values.length + 1 := by simp [offsetWords]
  constructor
  · refine ⟨Writer.emitBitmap_length values, ?_, ?_, joined.2.1,
      fun _ within => Writer.emitBitmap_valid values _ within, ?_⟩
    · rw [encodeColumn, Writer.emitWords_length, offsetsLength]
    · exact joined.2.2.trans (dataSize_sum values).symm
    · intro index within
      have offsetIndex : index < (offsetWords values).length := by
        rw [offsetsLength]
        omega
      have word : (offsetWords values)[index] = dataSize (values.take index) :=
        List.getElem_scanl offsetIndex
      have size : dataSize values = dataSize (values.take index) + dataSize (values.drop index) := by
        have all := List.take_append_drop index values
        conv_lhs => rw [← all]
        unfold dataSize
        rw [List.foldl_append]
        exact dataSize_prefix (values.drop index) _
      have cap : width.signedLimit ≤ 256^width.bytes := by cases width <;> decide
      change (Writer.emitWords width.bytes (offsetWords values)).readLE
        (width.bytes * index) width.bytes = _
      rw [Writer.readLE_emitWords _ _ _ offsetIndex, word, Nat.mod_eq_of_lt (by omega)]
  · intro part mem
    simp only [columnPartsFor, encodeColumn, List.mem_cons, List.mem_nil_iff, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact Writer.emitWords_wf _ _
    · exact Writer.emitWords_wf _ _
    · exact joined.1

private theorem record_checked {width : Binary.Offsets.Width} {limits : Limits}
    {nullable : Bool} {values : Binary.Column} {wire : KBytes}
    (written : emitRecordFor width limits nullable values = .ok wire) :
    ∃ node, checkRecordFor width limits nullable values = .ok node ∧
      let packed := Writer.packBuffers 0 (columnPartsFor width values)
      Arrow.StreamWriter.emitFrame limits
        ⟨.recordBatch ⟨node.length, [node], packed.1⟩, packed.2.len⟩ packed.2 = .ok wire := by
  unfold emitRecordFor at written
  cases admitted : checkRecordFor width limits nullable values with
  | error cause => simp [admitted, Bind.bind, Except.bind] at written
  | ok node =>
    refine ⟨node, rfl, ?_⟩
    generalize packed : Writer.packBuffers 0 (columnPartsFor width values) = pair at written ⊢
    obtain ⟨descriptors, body⟩ := pair
    cases frame : Arrow.StreamWriter.emitFrame limits
        ⟨.recordBatch ⟨node.length, [node], descriptors⟩, body.len⟩ body with
    | error cause => simp [admitted, frame, Bind.bind, Except.bind, Except.mapError] at written
    | ok bytes =>
      simp [admitted, frame, Bind.bind, Except.bind, Except.mapError] at written
      subst bytes
      exact frame

private theorem packLength (start : Nat) (parts : List KBytes) :
    (Writer.packBuffers start parts).2.len =
      (parts.map fun part => part.len + Writer.padding part.len).sum := by
  induction parts generalizing start with
  | nil => rfl
  | cons first rest ih =>
    change first.len + (Writer.padding first.len +
      (Writer.packBuffers (start + first.len + Writer.padding first.len) rest).2.len) = _
    rw [ih]
    simp [Nat.add_assoc]

theorem emitRecordFor_exact {width : Binary.Offsets.Width} {limits : Limits}
    {nullable : Bool} {values : Binary.Column} {wire : KBytes}
    (written : emitRecordFor width limits nullable values = .ok wire) :
    RecordWire width limits values wire := by
  obtain ⟨node, checked, framed⟩ := record_checked written
  obtain ⟨rfl, bounds, wf⟩ := checkRecord_exact checked
  obtain ⟨column, parts⟩ := encoded_exact bounds.2.1 wf
  have len : (Writer.packBuffers 0 (columnPartsFor width values)).2.len =
      bodySizeFor width values.length (dataSize values) := by
    rw [packLength]
    simp only [columnPartsFor, bodySizeFor, List.map_cons, List.map_nil, column.1, column.2.1, column.2.2.1]
  exact ⟨bounds, column, Writer.packBuffers_exact _ parts, len,
    Arrow.StreamWriter.emitFrame_exact framed⟩

private theorem prefix_metadata_bound {limits : Limits} {name : String} {envelope : Envelope}
    (admitted : readPrefix limits 0xffffffff (Wire.schemaSizeFor name) = .ok envelope) :
    Wire.schemaSizeFor name ≤ limits.metadataBytes := by
  by_cases large : Wire.schemaSizeFor name > limits.metadataBytes
  · have nonzero : Wire.schemaSizeFor name ≠ 0 := by simp [Wire.schemaSizeFor]
    simp [readPrefix, nonzero, large] at admitted
    split at admitted <;> contradiction
  · omega

theorem serializeFor_exact {width : Binary.Offsets.Width} {limits : Limits}
    {name : String} {nullable : Bool} {batches : List Binary.Column} {wire : KBytes}
    (written : serializeFor width limits name nullable batches = .ok wire) :
    SerializedWire width limits name nullable batches wire := by
  by_cases fields : limits.fields = 0
  · simp [serializeFor, fields] at written
  by_cases count : batches.length > limits.batches
  · simp [serializeFor, fields, count] at written
  cases admitted : readPrefix limits 0xffffffff (Wire.schemaSizeFor name) with
  | error cause =>
    simp [serializeFor, fields, count, admitted, Bind.bind, Except.bind, Except.mapError] at written
  | ok envelope =>
    let write := fun (pair : Binary.Column × Nat) =>
      (emitRecordFor width limits nullable pair.1).mapError (Error.record pair.2)
    have header : (readPrefix limits 0xffffffff (Wire.schemaSizeFor name)).mapError Error.ipc =
        .ok envelope := by rw [admitted]; rfl
    simp only [serializeFor, fields, count, ite_false, header, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at written
    cases serialized : batches.zipIdx.mapM write with
    | error cause =>
      have frames := serialized
      dsimp only [write] at frames
      rw [frames] at written
      cases written
    | ok records =>
      have frames := serialized
      dsimp only [write] at frames
      rw [frames] at written
      cases written
      have pairs : List.Forall₂ (fun (pair : Binary.Column × Nat) frame =>
          RecordWire width limits pair.1 frame) batches.zipIdx records := by
        apply (List.mapM_eq_ok_iff_forall₂.mp serialized).imp
        intro pair frame emitted
        cases frameEq : emitRecordFor width limits nullable pair.1 with
        | error cause => simp [write, frameEq, Except.mapError] at emitted
        | ok bytes =>
          simp [write, frameEq, Except.mapError] at emitted
          subst bytes
          exact emitRecordFor_exact frameEq
      have ordered : List.Forall₂ (RecordWire width limits) batches records :=
        List.zipIdx_map_fst 0 batches ▸ List.forall₂_map_left_iff.mpr pairs
      refine ⟨⟨Nat.pos_of_ne_zero fields, prefix_metadata_bound admitted, Nat.le_of_not_gt count, ?_⟩,
        records, ordered, rfl⟩
      intro values occurs
      obtain ⟨i, within, rfl⟩ := List.mem_iff_getElem.mp occurs
      have withinFrames : i < records.length := ordered.length_eq ▸ within
      exact (ordered.get within withinFrames).1

end Silmaril.Proofs.Formats.Arrow.Binary.StreamWriter
