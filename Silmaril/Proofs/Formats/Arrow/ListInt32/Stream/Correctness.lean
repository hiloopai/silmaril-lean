module

public import Silmaril.Formats.Arrow.ListInt32.Stream.Defs
import Silmaril.Formats.Arrow.Body.Thms
import Silmaril.Formats.Arrow.Framing.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.ListInt32.Stream

open Silmaril.Formats.Arrow hiding Limits Row readRows
open Silmaril.Formats.Arrow.ListInt32.Stream

public theorem readRow_wire {bitmap offsets : KBytes} {children : Array (Option Int32)}
    {index : Nat} {row : Row} (h : readRow bitmap offsets children index = .ok row) :
    RowWire bitmap offsets children index row := by
  unfold readRow at h
  cases first : Body.offsetAt offsets index with
  | none => simp [first] at h
  | some lo =>
    simp only [first] at h
    cases second : Body.offsetAt offsets (index + 1) with
    | none => simp [second] at h
    | some hi =>
      simp only [second] at h
      split at h
      · contradiction
      · rename_i range
        have bounds := Decidable.of_not_not range
        cases validity : Body.validAt bitmap index with
        | none => simp [validity] at h
        | some valid =>
          simp only [validity, Pure.pure, Except.pure] at h
          obtain rfl := Except.ok.inj h
          exact ⟨valid, lo, hi, validity, first, second, bounds.1, bounds.2, by simp⟩

private theorem rows_wire {bitmap offsets : KBytes} {children : Array (Option Int32)}
    {indices : List Nat} {rows : List Row}
    (h : indices.mapM (readRow bitmap offsets children) = .ok rows) :
    List.Forall₂ (RowWire bitmap offsets children) indices rows ∧ rows.length = indices.length := by
  induction indices generalizing rows with
  | nil =>
    obtain rfl := Except.ok.inj h
    exact ⟨.nil, rfl⟩
  | cons index rest ih =>
    rw [List.mapM_cons] at h
    cases first : readRow bitmap offsets children index with
    | error e => simp [first, Bind.bind, Except.bind] at h
    | ok row =>
      simp only [first, Bind.bind, Except.bind] at h
      cases tail : rest.mapM (readRow bitmap offsets children) with
      | error e => simp [tail] at h
      | ok more =>
        rw [tail] at h
        obtain rfl := Except.ok.inj h
        obtain ⟨all, count⟩ := ih tail
        exact ⟨.cons (readRow_wire first) all, by simp [count]⟩

private theorem cells_length {buffers : Body.ColumnBuffers} {indices : List Nat} {column : Column}
    (h : Body.CellsWire buffers indices column) : column.length = indices.length := by
  induction indices generalizing column with
  | nil => cases column <;> simp_all [Body.CellsWire]
  | cons index rest ih => cases column <;> simp_all [Body.CellsWire]

public theorem readRows_wire {layout : Layout} {body : KBytes} {rows : List Row}
    (h : readRows layout body = .ok rows) : RowsWire layout body rows := by
  unfold readRows at h
  split at h
  · contradiction
  · rename_i fit
    dsimp only at h
    split at h
    · contradiction
    · rename_i bitmap
      split at h
      · contradiction
      · rename_i offsets
        have endpoints :
            (Body.sliceBuffer body layout.offsets).len = 4 * (layout.parent.length + 1) ∧
            Body.offsetAt (Body.sliceBuffer body layout.offsets) 0 = some 0 ∧
            Body.offsetAt (Body.sliceBuffer body layout.offsets) layout.parent.length =
              some layout.child.length := by simpa [and_assoc] using offsets
        cases child : Body.readColumn layout.child (layout.childBuffers body) with
        | error e => simp [child, Except.mapError, Bind.bind, Except.bind] at h
        | ok physical =>
          simp only [child, Except.mapError, Bind.bind, Except.bind] at h
          cases decoded : (List.range layout.parent.length).mapM
              (readRow (Body.sliceBuffer body layout.parentValidity)
                (Body.sliceBuffer body layout.offsets) (physical.map int32Slot).toArray) with
          | error e => simp [decoded] at h
          | ok result =>
            simp only [decoded] at h
            split at h
            · contradiction
            · rename_i nulls
              obtain rfl := Except.ok.inj h
              obtain ⟨slots, count⟩ := rows_wire decoded
              have childWire := (Body.readColumn_iff _ _ _).mp child
              have childCount : physical.length = layout.child.length := by
                simpa using cells_length childWire.2.2.1
              exact ⟨Decidable.of_not_not fit, Decidable.of_not_not bitmap, endpoints.1, endpoints.2.1,
                endpoints.2.2, Decidable.of_not_not nulls, by simpa using count, physical,
                childCount, childWire, slots⟩

private theorem layout_wire {metadata : RecordBatch} {layout : Layout}
    (h : layoutOf metadata = .ok layout) :
    layout.parent.length = metadata.rowCount ∧
      metadata.nodes = [layout.parent, layout.child] ∧ metadata.buffers = layout.buffers := by
  unfold layoutOf at h
  split at h
  · split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨by assumption, by assumption, by assumption⟩
    · contradiction
  · contradiction

public theorem readRecord_wire {limits : Limits} {input : KBytes}
    {rowsBefore childrenBefore offset size : Nat} {batch : Batch}
    (h : readRecord limits input rowsBefore childrenBefore offset size = .ok batch) :
    RecordWire limits input rowsBefore childrenBefore offset size batch := by
  unfold readRecord at h
  cases parsed : readMessage { limits.ipc with fields := min 2 limits.ipc.fields }
      (input.slice (offset + 8) size) with
  | error e => simp [parsed, Except.mapError, Bind.bind, Except.bind] at h
  | ok message =>
    simp only [parsed, Except.mapError, Bind.bind, Except.bind] at h
    split at h
    · rename_i metadata kind
      cases bound : layoutOf metadata with
      | error e => simp [bound] at h
      | ok layout =>
        simp only [bound] at h
        split at h
        · contradiction
        · rename_i rowCap
          split at h
          · contradiction
          · rename_i childCap
            cases bodyRead : readBody limits.ipc input (offset + 8 + size) message.bodyLength with
            | error e => simp [bodyRead] at h
            | ok body =>
              simp only [bodyRead] at h
              cases decoded : readRows layout body with
              | error e => simp [decoded] at h
              | ok rows =>
                simp only [decoded] at h
                obtain rfl := Except.ok.inj h
                obtain ⟨count, nodes, buffers⟩ := layout_wire bound
                have header : message = ⟨.recordBatch metadata, message.bodyLength⟩ := by
                  cases message
                  simp_all
                exact ⟨metadata, layout, body, header ▸ parsed, bound, count, nodes, buffers, bodyRead,
                  readRows_wire decoded, rfl, rfl, rfl, Nat.le_of_not_gt rowCap, Nat.le_of_not_gt childCap⟩
    · contradiction

public theorem readBatches_wire {limits : Limits} {input : KBytes}
    {fuel index rowsBefore childrenBefore offset : Nat} {batches : List Batch}
    (h : readBatches limits input fuel index rowsBefore childrenBefore offset = .ok batches) :
    BatchesWire limits input fuel rowsBefore childrenBefore offset batches := by
  induction fuel generalizing index rowsBefore childrenBefore offset batches with
  | zero =>
    rw [readBatches] at h
    cases envelope : readEnvelope limits.ipc input offset with
    | error e => simp [envelope, Except.mapError, Bind.bind, Except.bind] at h
    | ok env =>
      cases env with
      | metadata size => simp [envelope, Except.mapError, Bind.bind, Except.bind] at h
      | eos =>
        by_cases extent : offset + 8 = input.len
        · have same : [] = batches := Except.ok.inj (by
            simpa only [envelope, extent, Except.mapError, Bind.bind, Except.bind, ite_eq_left, Pure.pure, Except.pure] using h)
          subst batches
          exact .eos envelope extent
        · simp [envelope, extent, Except.mapError, Bind.bind, Except.bind] at h
  | succ fuel ih =>
    rw [readBatches] at h
    cases envelope : readEnvelope limits.ipc input offset with
    | error e => simp [envelope, Except.mapError, Bind.bind, Except.bind] at h
    | ok env =>
      cases env with
      | eos =>
        by_cases extent : offset + 8 = input.len
        · have same : [] = batches := Except.ok.inj (by
            simpa only [envelope, extent, Except.mapError, Bind.bind, Except.bind, ite_eq_left, Pure.pure, Except.pure] using h)
          subst batches
          exact .eos envelope extent
        · simp [envelope, extent, Except.mapError, Bind.bind, Except.bind] at h
      | metadata size =>
        simp only [envelope, Except.mapError, Bind.bind, Except.bind] at h
        cases record : readRecord limits input rowsBefore childrenBefore offset size with
        | error e => simp [record] at h
        | ok batch =>
          simp only [record] at h
          cases later : readBatches limits input fuel (index + 1) (rowsBefore + batch.rows.length)
              (childrenBefore + batch.childCount) batch.next with
          | error e => simp [later] at h
          | ok rest =>
            rw [later] at h
            obtain rfl := Except.ok.inj h
            exact .next envelope (readRecord_wire record) (ih later)

public theorem checkParents_required {batches : List Batch} (h : checkParents false batches = .ok ()) :
    ∀ batch ∈ batches, ∀ row ∈ batch.rows, row.isSome = true := by
  intro batch member row belongs
  unfold checkParents at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases found : batches.findIdx? (fun batch => batch.rows.any Option.isNone) with
  | some index => simp [found] at h
  | none =>
    have valid := List.findIdx?_eq_none_iff.mp found batch member
    have nonnull := List.any_eq_false.mp valid row belongs
    cases row <;> simp_all

public theorem readFor_wire {parentNullable : Bool} {limits : Limits} {input : KBytes} {observed : Observed}
    (h : readFor parentNullable limits input = .ok observed) :
    input.wf = true ∧ ∃ size,
      readEnvelope limits.ipc input 0 = .ok (.metadata size) ∧
      ListInt32.readSchemaFor parentNullable limits.ipc (input.slice 8 size) = .ok observed.field ∧
      BatchesWire limits input limits.ipc.batches 0 0 (8 + size) observed.batches ∧
      checkParents parentNullable observed.batches = .ok () := by
  unfold readFor at h
  split at h
  · contradiction
  · rename_i wf
    have source : input.wf = true := by simpa using wf
    unfold readSchemaFrameFor at h
    cases envelope : readEnvelope limits.ipc input 0 with
    | error e => simp [envelope, Except.mapError, Bind.bind, Except.bind] at h
    | ok env =>
      cases env with
      | eos => simp [envelope, Except.mapError, Bind.bind, Except.bind] at h
      | metadata size =>
        simp only [envelope, Except.mapError, Bind.bind, Except.bind] at h
        cases schema : ListInt32.readSchemaFor parentNullable limits.ipc (input.slice 8 size) with
        | error e => simp [schema] at h
        | ok field =>
          simp only [schema, Pure.pure, Except.pure] at h
          cases decoded : readBatches limits input limits.ipc.batches 0 0 0 (8 + size) with
          | error e => simp [decoded] at h
          | ok batches =>
            rw [decoded] at h
            cases parents : checkParents parentNullable batches with
            | error cause => simp [parents] at h
            | ok accepted =>
              cases accepted
              simp only [parents] at h
              obtain rfl := Except.ok.inj h
              exact ⟨source, size, rfl, schema, readBatches_wire decoded, parents⟩

public theorem read_wire {limits : Limits} {input : KBytes} {observed : Observed}
    (h : read limits input = .ok observed) :
    input.wf = true ∧ ∃ size,
      readEnvelope limits.ipc input 0 = .ok (.metadata size) ∧
      ListInt32.readSchema limits.ipc (input.slice 8 size) = .ok observed.field ∧
      BatchesWire limits input limits.ipc.batches 0 0 (8 + size) observed.batches := by
  obtain ⟨wf, size, frame, schema, batches, _⟩ := readFor_wire h
  exact ⟨wf, size, frame, schema, batches⟩

public theorem record_ranges {limits : Limits} {input : KBytes}
    {rowsBefore childrenBefore offset size : Nat} {batch : Batch}
    (wf : input.wf = true) (envelope : readEnvelope limits.ipc input offset = .ok (.metadata size))
    (wire : RecordWire limits input rowsBefore childrenBefore offset size batch) :
    offset < batch.next ∧ batch.next ≤ input.len ∧
    (input.slice (offset + 8) size).toList = (input.toList.drop (offset + 8)).take size ∧
    ∃ body : KBytes, body.len = batch.bodyLength ∧
      body.toList = (input.toList.drop (offset + 8 + size)).take batch.bodyLength := by
  obtain ⟨metadata, layout, body, _, _, _, _, _, bodyRead, _, offsetEq, sizeEq, _, _, _⟩ := wire.data
  have extent := (readBody_iff _ _ _ _ _).mp bodyRead
  refine ⟨?_, ?_, metadata_exact wf envelope, body, body_exact wf bodyRead⟩
  · rw [Batch.next, offsetEq, sizeEq]
    omega
  · simpa [Batch.next, offsetEq, sizeEq] using extent.2.2.2.1

public theorem batches_length_le {limits : Limits} {input : KBytes} {fuel rows children offset : Nat}
    {batches : List Batch} (wire : BatchesWire limits input fuel rows children offset batches) :
    batches.length ≤ fuel := by
  induction wire with
  | eos => simp
  | next _ _ _ ih => simpa using Nat.succ_le_succ ih

end Silmaril.Proofs.Formats.Arrow.ListInt32.Stream
